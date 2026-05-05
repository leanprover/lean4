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
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
lean_object* l_List_lengthTR___redArg(lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0_value;
static const lean_ctor_object l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0_value)}};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_42_);
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
lean_dec_ref(v___x_83_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(lean_object* v_arity_173_, lean_object* v_b_174_){
_start:
{
lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_206_; 
v_fst_175_ = lean_ctor_get(v_b_174_, 0);
v_snd_176_ = lean_ctor_get(v_b_174_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_b_174_);
if (v_isSharedCheck_206_ == 0)
{
v___x_178_ = v_b_174_;
v_isShared_179_ = v_isSharedCheck_206_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_snd_176_);
lean_inc(v_fst_175_);
lean_dec(v_b_174_);
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
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_args_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_e_201_; lean_object* v___x_203_; 
v___x_192_ = lean_unsigned_to_nat(2u);
v___x_193_ = l_Lean_Expr_getAppNumArgs(v_fst_175_);
v___x_194_ = lean_nat_sub(v___x_193_, v___x_192_);
v___x_195_ = lean_nat_sub(v___x_194_, v___x_181_);
lean_dec(v___x_194_);
v___x_196_ = l_Lean_Expr_getRevArg_x21(v_fst_175_, v___x_195_);
v_args_197_ = lean_array_push(v_snd_176_, v___x_196_);
v___x_198_ = lean_unsigned_to_nat(3u);
v___x_199_ = lean_nat_sub(v___x_193_, v___x_198_);
lean_dec(v___x_193_);
v___x_200_ = lean_nat_sub(v___x_199_, v___x_181_);
lean_dec(v___x_199_);
v_e_201_ = l_Lean_Expr_getRevArg_x21(v_fst_175_, v___x_200_);
lean_dec(v_fst_175_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_args_197_);
lean_ctor_set(v___x_178_, 0, v_e_201_);
v___x_203_ = v___x_178_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_e_201_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_args_197_);
v___x_203_ = v_reuseFailAlloc_205_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
v_b_174_ = v___x_203_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___boxed(lean_object* v_arity_207_, lean_object* v_b_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(v_arity_207_, v_b_208_);
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
v___x_220_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(v_arity_214_, v___x_219_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(lean_object* v_upperBound_237_, lean_object* v_a_238_, lean_object* v_b_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = lean_nat_dec_lt(v_a_238_, v_upperBound_237_);
if (v___x_240_ == 0)
{
lean_dec(v_a_238_);
return v_b_239_;
}
else
{
lean_object* v_fst_241_; lean_object* v_snd_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_257_; 
v_fst_241_ = lean_ctor_get(v_b_239_, 0);
v_snd_242_ = lean_ctor_get(v_b_239_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_b_239_);
if (v_isSharedCheck_257_ == 0)
{
v___x_244_ = v_b_239_;
v_isShared_245_ = v_isSharedCheck_257_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_snd_242_);
lean_inc(v_fst_241_);
lean_dec(v_b_239_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_257_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_unsigned_to_nat(1u);
v___x_248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
lean_inc(v_snd_242_);
v___x_249_ = l_Lean_mkProj(v___x_248_, v___x_246_, v_snd_242_);
v___x_250_ = lean_array_push(v_fst_241_, v___x_249_);
v___x_251_ = l_Lean_mkProj(v___x_248_, v___x_247_, v_snd_242_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_251_);
lean_ctor_set(v___x_244_, 0, v___x_250_);
v___x_253_ = v___x_244_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_251_);
v___x_253_ = v_reuseFailAlloc_256_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; 
v___x_254_ = lean_nat_add(v_a_238_, v___x_247_);
lean_dec(v_a_238_);
v_a_238_ = v___x_254_;
v_b_239_ = v___x_253_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg___boxed(lean_object* v_upperBound_258_, lean_object* v_a_259_, lean_object* v_b_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v_upperBound_258_, v_a_259_, v_b_260_);
lean_dec(v_upperBound_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(lean_object* v_t_262_, lean_object* v_arity_263_){
_start:
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_nat_dec_eq(v_arity_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_result_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_fst_271_; lean_object* v_snd_272_; lean_object* v___x_273_; 
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_nat_sub(v_arity_263_, v___x_266_);
v_result_268_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v_result_268_);
lean_ctor_set(v___x_269_, 1, v_t_262_);
v___x_270_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v___x_267_, v___x_264_, v___x_269_);
lean_dec(v___x_267_);
v_fst_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_fst_271_);
v_snd_272_ = lean_ctor_get(v___x_270_, 1);
lean_inc(v_snd_272_);
lean_dec_ref(v___x_270_);
v___x_273_ = lean_array_push(v_fst_271_, v_snd_272_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; 
lean_dec_ref(v_t_262_);
v___x_274_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___boxed(lean_object* v_t_275_, lean_object* v_arity_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(v_t_275_, v_arity_276_);
lean_dec(v_arity_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(lean_object* v_upperBound_278_, lean_object* v_inst_279_, lean_object* v_R_280_, lean_object* v_a_281_, lean_object* v_b_282_, lean_object* v_c_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v_upperBound_278_, v_a_281_, v_b_282_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___boxed(lean_object* v_upperBound_285_, lean_object* v_inst_286_, lean_object* v_R_287_, lean_object* v_a_288_, lean_object* v_b_289_, lean_object* v_c_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(v_upperBound_285_, v_inst_286_, v_R_287_, v_a_288_, v_b_289_, v_c_290_);
lean_dec(v_upperBound_285_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(lean_object* v_msg_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___f_299_; lean_object* v___x_665__overap_300_; lean_object* v___x_301_; 
v___f_299_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_665__overap_300_ = lean_panic_fn_borrowed(v___f_299_, v_msg_293_);
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
v___x_301_ = lean_apply_5(v___x_665__overap_300_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, lean_box(0));
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___boxed(lean_object* v_msg_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v_msg_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(lean_object* v_k_309_, lean_object* v_b_310_, lean_object* v_c_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; 
lean_inc(v___y_315_);
lean_inc_ref(v___y_314_);
lean_inc(v___y_313_);
lean_inc_ref(v___y_312_);
v___x_317_ = lean_apply_7(v_k_309_, v_b_310_, v_c_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, lean_box(0));
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0___boxed(lean_object* v_k_318_, lean_object* v_b_319_, lean_object* v_c_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(v_k_318_, v_b_319_, v_c_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(lean_object* v_type_327_, lean_object* v_maxFVars_x3f_328_, lean_object* v_k_329_, uint8_t v_cleanupAnnotations_330_, uint8_t v_whnfType_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___f_337_; lean_object* v___x_338_; 
v___f_337_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_337_, 0, v_k_329_);
v___x_338_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_327_, v_maxFVars_x3f_328_, v___f_337_, v_cleanupAnnotations_330_, v_whnfType_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v_a_347_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_338_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_338_);
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
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___boxed(lean_object* v_type_355_, lean_object* v_maxFVars_x3f_356_, lean_object* v_k_357_, lean_object* v_cleanupAnnotations_358_, lean_object* v_whnfType_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_365_; uint8_t v_whnfType_boxed_366_; lean_object* v_res_367_; 
v_cleanupAnnotations_boxed_365_ = lean_unbox(v_cleanupAnnotations_358_);
v_whnfType_boxed_366_ = lean_unbox(v_whnfType_359_);
v_res_367_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_355_, v_maxFVars_x3f_356_, v_k_357_, v_cleanupAnnotations_boxed_365_, v_whnfType_boxed_366_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(lean_object* v_00_u03b1_368_, lean_object* v_type_369_, lean_object* v_maxFVars_x3f_370_, lean_object* v_k_371_, uint8_t v_cleanupAnnotations_372_, uint8_t v_whnfType_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_369_, v_maxFVars_x3f_370_, v_k_371_, v_cleanupAnnotations_372_, v_whnfType_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___boxed(lean_object* v_00_u03b1_380_, lean_object* v_type_381_, lean_object* v_maxFVars_x3f_382_, lean_object* v_k_383_, lean_object* v_cleanupAnnotations_384_, lean_object* v_whnfType_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_391_; uint8_t v_whnfType_boxed_392_; lean_object* v_res_393_; 
v_cleanupAnnotations_boxed_391_ = lean_unbox(v_cleanupAnnotations_384_);
v_whnfType_boxed_392_ = lean_unbox(v_whnfType_385_);
v_res_393_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(v_00_u03b1_380_, v_type_381_, v_maxFVars_x3f_382_, v_k_383_, v_cleanupAnnotations_boxed_391_, v_whnfType_boxed_392_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(lean_object* v___x_394_, lean_object* v_type_395_, uint8_t v___x_396_, uint8_t v___x_397_, lean_object* v_tuple_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_inc_ref(v_tuple_398_);
v___x_404_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(v_tuple_398_, v___x_394_);
v___x_405_ = l_Lean_Meta_instantiateForall(v_type_395_, v___x_404_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec_ref(v___x_404_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v___x_405_);
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_mk_empty_array_with_capacity(v___x_407_);
v___x_409_ = lean_array_push(v___x_408_, v_tuple_398_);
v___x_410_ = 1;
v___x_411_ = l_Lean_Meta_mkForallFVars(v___x_409_, v_a_406_, v___x_396_, v___x_397_, v___x_397_, v___x_410_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec_ref(v___x_409_);
return v___x_411_;
}
else
{
lean_dec_ref(v_tuple_398_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed(lean_object* v___x_412_, lean_object* v_type_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v_tuple_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
uint8_t v___x_1465__boxed_422_; uint8_t v___x_1466__boxed_423_; lean_object* v_res_424_; 
v___x_1465__boxed_422_ = lean_unbox(v___x_414_);
v___x_1466__boxed_423_ = lean_unbox(v___x_415_);
v_res_424_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(v___x_412_, v_type_413_, v___x_1465__boxed_422_, v___x_1466__boxed_423_, v_tuple_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___x_412_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(lean_object* v_k_425_, lean_object* v_b_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
v___x_432_ = lean_apply_6(v_k_425_, v_b_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, lean_box(0));
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_433_, lean_object* v_b_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(v_k_433_, v_b_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(lean_object* v_name_441_, uint8_t v_bi_442_, lean_object* v_type_443_, lean_object* v_k_444_, uint8_t v_kind_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___f_451_; lean_object* v___x_452_; 
v___f_451_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_451_, 0, v_k_444_);
v___x_452_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_441_, v_bi_442_, v_type_443_, v___f_451_, v_kind_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_452_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_452_);
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
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___boxed(lean_object* v_name_469_, lean_object* v_bi_470_, lean_object* v_type_471_, lean_object* v_k_472_, lean_object* v_kind_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
uint8_t v_bi_boxed_479_; uint8_t v_kind_boxed_480_; lean_object* v_res_481_; 
v_bi_boxed_479_ = lean_unbox(v_bi_470_);
v_kind_boxed_480_ = lean_unbox(v_kind_473_);
v_res_481_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_469_, v_bi_boxed_479_, v_type_471_, v_k_472_, v_kind_boxed_480_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(lean_object* v_name_482_, lean_object* v_type_483_, lean_object* v_k_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v___x_490_; uint8_t v___x_491_; lean_object* v___x_492_; 
v___x_490_ = 0;
v___x_491_ = 0;
v___x_492_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_482_, v___x_490_, v_type_483_, v_k_484_, v___x_491_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg___boxed(lean_object* v_name_493_, lean_object* v_type_494_, lean_object* v_k_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_493_, v_type_494_, v_k_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_501_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_504_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__1));
v___x_505_ = lean_unsigned_to_nat(6u);
v___x_506_ = lean_unsigned_to_nat(138u);
v___x_507_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__0));
v___x_508_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_509_ = l_mkPanicMessageWithDecl(v___x_508_, v___x_507_, v___x_506_, v___x_505_, v___x_504_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(lean_object* v___x_513_, lean_object* v_type_514_, uint8_t v___x_515_, uint8_t v___x_516_, lean_object* v_varNames_517_, lean_object* v___x_518_, lean_object* v_xs_519_, lean_object* v_x_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_array_get_size(v_xs_519_);
v___x_527_ = lean_nat_dec_eq(v___x_526_, v___x_513_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec_ref(v_xs_519_);
lean_dec_ref(v_type_514_);
v___x_528_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2, &l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2);
v___x_529_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_528_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
return v___x_529_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Meta_ArgsPacker_Unary_packType(v_xs_519_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___f_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref(v___x_530_);
v___x_532_ = lean_box(v___x_515_);
v___x_533_ = lean_box(v___x_516_);
v___f_534_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed), 10, 4);
lean_closure_set(v___f_534_, 0, v___x_526_);
lean_closure_set(v___f_534_, 1, v_type_514_);
lean_closure_set(v___f_534_, 2, v___x_532_);
lean_closure_set(v___f_534_, 3, v___x_533_);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_dec_eq(v___x_526_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_538_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_537_, v_a_531_, v___f_534_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = lean_box(0);
v___x_540_ = lean_array_get_borrowed(v___x_539_, v_varNames_517_, v___x_518_);
lean_inc(v___x_540_);
v___x_541_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_540_, v_a_531_, v___f_534_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
return v___x_541_;
}
}
else
{
lean_dec_ref(v_type_514_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed(lean_object* v___x_542_, lean_object* v_type_543_, lean_object* v___x_544_, lean_object* v___x_545_, lean_object* v_varNames_546_, lean_object* v___x_547_, lean_object* v_xs_548_, lean_object* v_x_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___x_1618__boxed_555_; uint8_t v___x_1619__boxed_556_; lean_object* v_res_557_; 
v___x_1618__boxed_555_ = lean_unbox(v___x_544_);
v___x_1619__boxed_556_ = lean_unbox(v___x_545_);
v_res_557_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(v___x_542_, v_type_543_, v___x_1618__boxed_555_, v___x_1619__boxed_556_, v_varNames_546_, v___x_547_, v_xs_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec_ref(v_x_549_);
lean_dec(v___x_547_);
lean_dec_ref(v_varNames_546_);
lean_dec(v___x_542_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType(lean_object* v_varNames_558_, lean_object* v_type_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_array_get_size(v_varNames_558_);
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_nat_dec_eq(v___x_565_, v___x_566_);
if (v___x_567_ == 0)
{
uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___f_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_568_ = 1;
v___x_569_ = lean_box(v___x_567_);
v___x_570_ = lean_box(v___x_568_);
lean_inc_ref(v_type_559_);
v___f_571_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed), 13, 6);
lean_closure_set(v___f_571_, 0, v___x_565_);
lean_closure_set(v___f_571_, 1, v_type_559_);
lean_closure_set(v___f_571_, 2, v___x_569_);
lean_closure_set(v___f_571_, 3, v___x_570_);
lean_closure_set(v___f_571_, 4, v_varNames_558_);
lean_closure_set(v___f_571_, 5, v___x_566_);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_565_);
v___x_573_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_559_, v___x_572_, v___f_571_, v___x_567_, v___x_567_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec_ref(v_varNames_558_);
v___x_574_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_575_ = l_Lean_mkArrow(v___x_574_, v_type_559_, v_a_562_, v_a_563_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___boxed(lean_object* v_varNames_576_, lean_object* v_type_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_varNames_576_, v_type_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(lean_object* v_00_u03b1_584_, lean_object* v_name_585_, uint8_t v_bi_586_, lean_object* v_type_587_, lean_object* v_k_588_, uint8_t v_kind_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_585_, v_bi_586_, v_type_587_, v_k_588_, v_kind_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___boxed(lean_object* v_00_u03b1_596_, lean_object* v_name_597_, lean_object* v_bi_598_, lean_object* v_type_599_, lean_object* v_k_600_, lean_object* v_kind_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
uint8_t v_bi_boxed_607_; uint8_t v_kind_boxed_608_; lean_object* v_res_609_; 
v_bi_boxed_607_ = lean_unbox(v_bi_598_);
v_kind_boxed_608_ = lean_unbox(v_kind_601_);
v_res_609_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(v_00_u03b1_596_, v_name_597_, v_bi_boxed_607_, v_type_599_, v_k_600_, v_kind_boxed_608_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(lean_object* v_00_u03b1_610_, lean_object* v_name_611_, lean_object* v_type_612_, lean_object* v_k_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_611_, v_type_612_, v_k_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___boxed(lean_object* v_00_u03b1_620_, lean_object* v_name_621_, lean_object* v_type_622_, lean_object* v_k_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(v_00_u03b1_620_, v_name_621_, v_type_622_, v_k_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(lean_object* v_msgData_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___x_636_; lean_object* v_env_637_; lean_object* v___x_638_; lean_object* v_mctx_639_; lean_object* v_lctx_640_; lean_object* v_options_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_636_ = lean_st_ref_get(v___y_634_);
v_env_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_env_637_);
lean_dec(v___x_636_);
v___x_638_ = lean_st_ref_get(v___y_632_);
v_mctx_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc_ref(v_mctx_639_);
lean_dec(v___x_638_);
v_lctx_640_ = lean_ctor_get(v___y_631_, 2);
v_options_641_ = lean_ctor_get(v___y_633_, 2);
lean_inc_ref(v_options_641_);
lean_inc_ref(v_lctx_640_);
v___x_642_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_642_, 0, v_env_637_);
lean_ctor_set(v___x_642_, 1, v_mctx_639_);
lean_ctor_set(v___x_642_, 2, v_lctx_640_);
lean_ctor_set(v___x_642_, 3, v_options_641_);
v___x_643_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v_msgData_630_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0___boxed(lean_object* v_msgData_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msgData_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_ref_658_; lean_object* v___x_659_; lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_668_; 
v_ref_658_ = lean_ctor_get(v___y_655_, 5);
v___x_659_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msg_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_668_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
lean_inc(v_ref_658_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v_ref_658_);
lean_ctor_set(v___x_664_, 1, v_a_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 1);
lean_ctor_set(v___x_662_, 0, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg___boxed(lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_675_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0));
v___x_678_ = l_Lean_stringToMessageData(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed(lean_object** _args){
lean_object* v___x_679_ = _args[0];
lean_object* v___x_680_ = _args[1];
lean_object* v___x_681_ = _args[2];
lean_object* v_arg_682_ = _args[3];
lean_object* v_arg_683_ = _args[4];
lean_object* v_a_684_ = _args[5];
lean_object* v_alt_685_ = _args[6];
lean_object* v_tail_686_ = _args[7];
lean_object* v_u_687_ = _args[8];
lean_object* v___x_688_ = _args[9];
lean_object* v___x_689_ = _args[10];
lean_object* v___x_690_ = _args[11];
lean_object* v_head_691_ = _args[12];
lean_object* v_x_692_ = _args[13];
lean_object* v___y_693_ = _args[14];
lean_object* v___y_694_ = _args[15];
lean_object* v___y_695_ = _args[16];
lean_object* v___y_696_ = _args[17];
lean_object* v___y_697_ = _args[18];
_start:
{
uint8_t v___x_3515__boxed_698_; uint8_t v___x_3516__boxed_699_; uint8_t v___x_3517__boxed_700_; lean_object* v_res_701_; 
v___x_3515__boxed_698_ = lean_unbox(v___x_688_);
v___x_3516__boxed_699_ = lean_unbox(v___x_689_);
v___x_3517__boxed_700_ = lean_unbox(v___x_690_);
v_res_701_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(v___x_679_, v___x_680_, v___x_681_, v_arg_682_, v_arg_683_, v_a_684_, v_alt_685_, v_tail_686_, v_u_687_, v___x_3515__boxed_698_, v___x_3516__boxed_699_, v___x_3517__boxed_700_, v_head_691_, v_x_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(lean_object* v_varNames_706_, lean_object* v_e_707_, lean_object* v_u_708_, lean_object* v_codomain_709_, lean_object* v_alt_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
if (lean_obj_tag(v_varNames_706_) == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v_codomain_709_);
lean_dec(v_u_708_);
lean_dec_ref(v_e_707_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_alt_710_);
return v___x_716_;
}
else
{
lean_object* v_tail_717_; 
v_tail_717_ = lean_ctor_get(v_varNames_706_, 1);
lean_inc(v_tail_717_);
if (lean_obj_tag(v_tail_717_) == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec_ref(v_varNames_706_);
lean_dec_ref(v_codomain_709_);
lean_dec(v_u_708_);
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_mk_empty_array_with_capacity(v___x_718_);
v___x_720_ = lean_array_push(v___x_719_, v_e_707_);
v___x_721_ = l_Lean_Expr_beta(v_alt_710_, v___x_720_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
else
{
lean_object* v_head_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_779_; 
v_head_723_ = lean_ctor_get(v_varNames_706_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_varNames_706_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v_varNames_706_, 1);
lean_dec(v_unused_780_);
v___x_725_ = v_varNames_706_;
v_isShared_726_ = v_isSharedCheck_779_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_head_723_);
lean_dec(v_varNames_706_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_779_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_head_727_; lean_object* v___x_728_; 
v_head_727_ = lean_ctor_get(v_tail_717_, 0);
lean_inc(v_head_727_);
lean_inc(v_a_714_);
lean_inc_ref(v_a_713_);
lean_inc(v_a_712_);
lean_inc_ref(v_a_711_);
lean_inc_ref(v_e_707_);
v___x_728_ = lean_infer_type(v_e_707_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc_n(v_a_729_, 2);
lean_dec_ref(v___x_728_);
v___x_730_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_729_, v_a_712_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref(v___x_730_);
v___x_741_ = l_Lean_Expr_cleanupAnnotations(v_a_731_);
v___x_742_ = l_Lean_Expr_isApp(v___x_741_);
if (v___x_742_ == 0)
{
lean_dec_ref(v___x_741_);
lean_dec(v_head_727_);
lean_del_object(v___x_725_);
lean_dec(v_head_723_);
lean_dec_ref(v_tail_717_);
lean_dec_ref(v_alt_710_);
lean_dec_ref(v_codomain_709_);
lean_dec(v_u_708_);
lean_dec_ref(v_e_707_);
v___y_733_ = v_a_711_;
v___y_734_ = v_a_712_;
v___y_735_ = v_a_713_;
v___y_736_ = v_a_714_;
goto v___jp_732_;
}
else
{
lean_object* v_arg_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v_arg_743_ = lean_ctor_get(v___x_741_, 1);
lean_inc_ref(v_arg_743_);
v___x_744_ = l_Lean_Expr_appFnCleanup___redArg(v___x_741_);
v___x_745_ = l_Lean_Expr_isApp(v___x_744_);
if (v___x_745_ == 0)
{
lean_dec_ref(v___x_744_);
lean_dec_ref(v_arg_743_);
lean_dec(v_head_727_);
lean_del_object(v___x_725_);
lean_dec_ref(v_tail_717_);
lean_dec(v_head_723_);
lean_dec_ref(v_alt_710_);
lean_dec_ref(v_codomain_709_);
lean_dec(v_u_708_);
lean_dec_ref(v_e_707_);
v___y_733_ = v_a_711_;
v___y_734_ = v_a_712_;
v___y_735_ = v_a_713_;
v___y_736_ = v_a_714_;
goto v___jp_732_;
}
else
{
lean_object* v_arg_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_arg_746_ = lean_ctor_get(v___x_744_, 1);
lean_inc_ref(v_arg_746_);
v___x_747_ = l_Lean_Expr_appFnCleanup___redArg(v___x_744_);
v___x_748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0));
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_750_ = l_Lean_Expr_isConstOf(v___x_747_, v___x_749_);
lean_dec_ref(v___x_747_);
if (v___x_750_ == 0)
{
lean_dec_ref(v_arg_746_);
lean_dec_ref(v_arg_743_);
lean_dec(v_head_727_);
lean_del_object(v___x_725_);
lean_dec_ref(v_tail_717_);
lean_dec(v_head_723_);
lean_dec_ref(v_alt_710_);
lean_dec_ref(v_codomain_709_);
lean_dec(v_u_708_);
lean_dec_ref(v_e_707_);
v___y_733_ = v_a_711_;
v___y_734_ = v_a_712_;
v___y_735_ = v_a_713_;
v___y_736_ = v_a_714_;
goto v___jp_732_;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; 
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = lean_mk_empty_array_with_capacity(v___x_751_);
lean_inc_ref(v_e_707_);
lean_inc_ref(v___x_752_);
v___x_753_ = lean_array_push(v___x_752_, v_e_707_);
v___x_754_ = 0;
v___x_755_ = 1;
v___x_756_ = l_Lean_Meta_mkLambdaFVars(v___x_753_, v_codomain_709_, v___x_754_, v___x_750_, v___x_754_, v___x_750_, v___x_755_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec_ref(v___x_753_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v___x_764_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc_n(v_a_757_, 2);
lean_dec_ref(v___x_756_);
v___x_758_ = l_Lean_Expr_getAppFn(v_a_729_);
lean_dec(v_a_729_);
v___x_759_ = l_Lean_Expr_constLevels_x21(v___x_758_);
lean_dec_ref(v___x_758_);
v___x_760_ = lean_box(v___x_754_);
v___x_761_ = lean_box(v___x_750_);
v___x_762_ = lean_box(v___x_755_);
lean_inc(v_u_708_);
lean_inc_ref(v_arg_743_);
lean_inc_ref_n(v_arg_746_, 2);
lean_inc(v___x_759_);
v___f_763_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed), 19, 13);
lean_closure_set(v___f_763_, 0, v___x_752_);
lean_closure_set(v___f_763_, 1, v___x_748_);
lean_closure_set(v___f_763_, 2, v___x_759_);
lean_closure_set(v___f_763_, 3, v_arg_746_);
lean_closure_set(v___f_763_, 4, v_arg_743_);
lean_closure_set(v___f_763_, 5, v_a_757_);
lean_closure_set(v___f_763_, 6, v_alt_710_);
lean_closure_set(v___f_763_, 7, v_tail_717_);
lean_closure_set(v___f_763_, 8, v_u_708_);
lean_closure_set(v___f_763_, 9, v___x_760_);
lean_closure_set(v___f_763_, 10, v___x_761_);
lean_closure_set(v___f_763_, 11, v___x_762_);
lean_closure_set(v___f_763_, 12, v_head_727_);
v___x_764_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_723_, v_arg_746_, v___f_763_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_778_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_778_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_778_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_778_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3));
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v___x_759_);
lean_ctor_set(v___x_725_, 0, v_u_708_);
v___x_771_ = v___x_725_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_u_708_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_759_);
v___x_771_ = v_reuseFailAlloc_777_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_772_ = l_Lean_Expr_const___override(v___x_769_, v___x_771_);
v___x_773_ = l_Lean_mkApp5(v___x_772_, v_arg_746_, v_arg_743_, v_a_757_, v_e_707_, v_a_765_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_773_);
v___x_775_ = v___x_767_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_dec(v___x_759_);
lean_dec(v_a_757_);
lean_dec_ref(v_arg_746_);
lean_dec_ref(v_arg_743_);
lean_del_object(v___x_725_);
lean_dec(v_u_708_);
lean_dec_ref(v_e_707_);
return v___x_764_;
}
}
else
{
lean_dec_ref(v___x_752_);
lean_dec_ref(v_arg_746_);
lean_dec_ref(v_arg_743_);
lean_dec(v_a_729_);
lean_dec(v_head_727_);
lean_del_object(v___x_725_);
lean_dec_ref(v_tail_717_);
lean_dec(v_head_723_);
lean_dec_ref(v_alt_710_);
lean_dec(v_u_708_);
lean_dec_ref(v_e_707_);
return v___x_756_;
}
}
}
}
v___jp_732_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_737_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1);
v___x_738_ = l_Lean_MessageData_ofExpr(v_a_729_);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_739_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
return v___x_740_;
}
}
else
{
lean_dec(v_a_729_);
lean_dec(v_head_727_);
lean_del_object(v___x_725_);
lean_dec(v_head_723_);
lean_dec_ref(v_tail_717_);
lean_dec_ref(v_alt_710_);
lean_dec_ref(v_codomain_709_);
lean_dec(v_u_708_);
lean_dec_ref(v_e_707_);
return v___x_730_;
}
}
else
{
lean_dec(v_head_727_);
lean_del_object(v___x_725_);
lean_dec_ref(v_tail_717_);
lean_dec(v_head_723_);
lean_dec_ref(v_alt_710_);
lean_dec_ref(v_codomain_709_);
lean_dec(v_u_708_);
lean_dec_ref(v_e_707_);
return v___x_728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(lean_object* v___x_781_, lean_object* v___x_782_, lean_object* v_arg_783_, lean_object* v_arg_784_, lean_object* v_x_785_, lean_object* v___x_786_, lean_object* v_a_787_, lean_object* v_alt_788_, lean_object* v___x_789_, lean_object* v_tail_790_, lean_object* v_u_791_, uint8_t v___x_792_, uint8_t v___x_793_, uint8_t v___x_794_, lean_object* v_y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_801_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6));
v___x_802_ = l_Lean_Name_mkStr2(v___x_781_, v___x_801_);
v___x_803_ = l_Lean_Expr_const___override(v___x_802_, v___x_782_);
lean_inc_ref_n(v_y_795_, 2);
lean_inc_ref(v_x_785_);
v___x_804_ = l_Lean_mkApp4(v___x_803_, v_arg_783_, v_arg_784_, v_x_785_, v_y_795_);
v___x_805_ = lean_array_push(v___x_786_, v___x_804_);
v___x_806_ = l_Lean_Expr_beta(v_a_787_, v___x_805_);
v___x_807_ = l_Lean_Expr_beta(v_alt_788_, v___x_789_);
v___x_808_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_tail_790_, v_y_795_, v_u_791_, v___x_806_, v___x_807_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref(v___x_808_);
v___x_810_ = lean_unsigned_to_nat(2u);
v___x_811_ = lean_mk_empty_array_with_capacity(v___x_810_);
v___x_812_ = lean_array_push(v___x_811_, v_x_785_);
v___x_813_ = lean_array_push(v___x_812_, v_y_795_);
v___x_814_ = l_Lean_Meta_mkLambdaFVars(v___x_813_, v_a_809_, v___x_792_, v___x_793_, v___x_792_, v___x_793_, v___x_794_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec_ref(v___x_813_);
return v___x_814_;
}
else
{
lean_dec_ref(v_y_795_);
lean_dec_ref(v_x_785_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_815_ = _args[0];
lean_object* v___x_816_ = _args[1];
lean_object* v_arg_817_ = _args[2];
lean_object* v_arg_818_ = _args[3];
lean_object* v_x_819_ = _args[4];
lean_object* v___x_820_ = _args[5];
lean_object* v_a_821_ = _args[6];
lean_object* v_alt_822_ = _args[7];
lean_object* v___x_823_ = _args[8];
lean_object* v_tail_824_ = _args[9];
lean_object* v_u_825_ = _args[10];
lean_object* v___x_826_ = _args[11];
lean_object* v___x_827_ = _args[12];
lean_object* v___x_828_ = _args[13];
lean_object* v_y_829_ = _args[14];
lean_object* v___y_830_ = _args[15];
lean_object* v___y_831_ = _args[16];
lean_object* v___y_832_ = _args[17];
lean_object* v___y_833_ = _args[18];
lean_object* v___y_834_ = _args[19];
_start:
{
uint8_t v___x_3536__boxed_835_; uint8_t v___x_3537__boxed_836_; uint8_t v___x_3538__boxed_837_; lean_object* v_res_838_; 
v___x_3536__boxed_835_ = lean_unbox(v___x_826_);
v___x_3537__boxed_836_ = lean_unbox(v___x_827_);
v___x_3538__boxed_837_ = lean_unbox(v___x_828_);
v_res_838_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(v___x_815_, v___x_816_, v_arg_817_, v_arg_818_, v_x_819_, v___x_820_, v_a_821_, v_alt_822_, v___x_823_, v_tail_824_, v_u_825_, v___x_3536__boxed_835_, v___x_3537__boxed_836_, v___x_3538__boxed_837_, v_y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(lean_object* v___x_839_, lean_object* v___x_840_, lean_object* v___x_841_, lean_object* v_arg_842_, lean_object* v_arg_843_, lean_object* v_a_844_, lean_object* v_alt_845_, lean_object* v_tail_846_, lean_object* v_u_847_, uint8_t v___x_848_, uint8_t v___x_849_, uint8_t v___x_850_, lean_object* v_head_851_, lean_object* v_x_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___f_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_inc_ref(v_x_852_);
lean_inc_ref(v___x_839_);
v___x_858_ = lean_array_push(v___x_839_, v_x_852_);
v___x_859_ = lean_box(v___x_848_);
v___x_860_ = lean_box(v___x_849_);
v___x_861_ = lean_box(v___x_850_);
lean_inc_ref(v___x_858_);
lean_inc_ref(v_arg_843_);
v___f_862_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed), 20, 14);
lean_closure_set(v___f_862_, 0, v___x_840_);
lean_closure_set(v___f_862_, 1, v___x_841_);
lean_closure_set(v___f_862_, 2, v_arg_842_);
lean_closure_set(v___f_862_, 3, v_arg_843_);
lean_closure_set(v___f_862_, 4, v_x_852_);
lean_closure_set(v___f_862_, 5, v___x_839_);
lean_closure_set(v___f_862_, 6, v_a_844_);
lean_closure_set(v___f_862_, 7, v_alt_845_);
lean_closure_set(v___f_862_, 8, v___x_858_);
lean_closure_set(v___f_862_, 9, v_tail_846_);
lean_closure_set(v___f_862_, 10, v_u_847_);
lean_closure_set(v___f_862_, 11, v___x_859_);
lean_closure_set(v___f_862_, 12, v___x_860_);
lean_closure_set(v___f_862_, 13, v___x_861_);
v___x_863_ = l_Lean_Expr_beta(v_arg_843_, v___x_858_);
v___x_864_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_851_, v___x_863_, v___f_862_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___boxed(lean_object* v_varNames_865_, lean_object* v_e_866_, lean_object* v_u_867_, lean_object* v_codomain_868_, lean_object* v_alt_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_varNames_865_, v_e_866_, v_u_867_, v_codomain_868_, v_alt_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(lean_object* v_00_u03b1_876_, lean_object* v_msg_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___boxed(lean_object* v_00_u03b1_884_, lean_object* v_msg_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(v_00_u03b1_884_, v_msg_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_891_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_894_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_895_ = lean_unsigned_to_nat(23u);
v___x_896_ = lean_unsigned_to_nat(180u);
v___x_897_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0));
v___x_898_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_899_ = l_mkPanicMessageWithDecl(v___x_898_, v___x_897_, v___x_896_, v___x_895_, v___x_894_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(lean_object* v___x_900_, lean_object* v___x_901_, lean_object* v_varNames_902_, lean_object* v_e_903_, uint8_t v___x_904_, uint8_t v___x_905_, lean_object* v_xs_906_, lean_object* v_codomain_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_array_get_size(v_xs_906_);
v___x_914_ = lean_nat_dec_eq(v___x_913_, v___x_900_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec_ref(v_codomain_907_);
lean_dec_ref(v_e_903_);
lean_dec_ref(v_varNames_902_);
v___x_915_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2, &l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2);
v___x_916_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_915_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
return v___x_916_;
}
else
{
lean_object* v___x_917_; 
lean_inc_ref(v_codomain_907_);
v___x_917_ = l_Lean_Meta_getLevel(v_codomain_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref(v___x_917_);
v___x_919_ = lean_array_fget_borrowed(v_xs_906_, v___x_901_);
v___x_920_ = lean_array_to_list(v_varNames_902_);
lean_inc(v___x_919_);
v___x_921_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v___x_920_, v___x_919_, v_a_918_, v_codomain_907_, v_e_903_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; lean_object* v___x_926_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_921_);
v___x_923_ = lean_mk_empty_array_with_capacity(v___x_900_);
lean_inc(v___x_919_);
v___x_924_ = lean_array_push(v___x_923_, v___x_919_);
v___x_925_ = 1;
v___x_926_ = l_Lean_Meta_mkLambdaFVars(v___x_924_, v_a_922_, v___x_904_, v___x_905_, v___x_904_, v___x_905_, v___x_925_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec_ref(v___x_924_);
return v___x_926_;
}
else
{
return v___x_921_;
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v_codomain_907_);
lean_dec_ref(v_e_903_);
lean_dec_ref(v_varNames_902_);
v_a_927_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_917_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_917_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed(lean_object* v___x_935_, lean_object* v___x_936_, lean_object* v_varNames_937_, lean_object* v_e_938_, lean_object* v___x_939_, lean_object* v___x_940_, lean_object* v_xs_941_, lean_object* v_codomain_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
uint8_t v___x_987__boxed_948_; uint8_t v___x_988__boxed_949_; lean_object* v_res_950_; 
v___x_987__boxed_948_ = lean_unbox(v___x_939_);
v___x_988__boxed_949_ = lean_unbox(v___x_940_);
v_res_950_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(v___x_935_, v___x_936_, v_varNames_937_, v_e_938_, v___x_987__boxed_948_, v___x_988__boxed_949_, v_xs_941_, v_codomain_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec_ref(v_xs_941_);
lean_dec(v___x_936_);
lean_dec(v___x_935_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry(lean_object* v_varNames_956_, lean_object* v_e_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_963_ = lean_array_get_size(v_varNames_956_);
v___x_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = lean_nat_dec_eq(v___x_963_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
lean_inc(v_a_961_);
lean_inc_ref(v_a_960_);
lean_inc(v_a_959_);
lean_inc_ref(v_a_958_);
lean_inc_ref(v_e_957_);
v___x_966_ = lean_infer_type(v_e_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref(v___x_966_);
lean_inc_ref(v_varNames_956_);
v___x_968_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_varNames_956_, v_a_967_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; uint8_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___f_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v___x_968_);
v___x_970_ = 1;
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_box(v___x_965_);
v___x_973_ = lean_box(v___x_970_);
v___f_974_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed), 13, 6);
lean_closure_set(v___f_974_, 0, v___x_971_);
lean_closure_set(v___f_974_, 1, v___x_964_);
lean_closure_set(v___f_974_, 2, v_varNames_956_);
lean_closure_set(v___f_974_, 3, v_e_957_);
lean_closure_set(v___f_974_, 4, v___x_972_);
lean_closure_set(v___f_974_, 5, v___x_973_);
v___x_975_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_976_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_969_, v___x_975_, v___f_974_, v___x_965_, v___x_965_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
return v___x_976_;
}
else
{
lean_dec_ref(v_e_957_);
lean_dec_ref(v_varNames_956_);
return v___x_968_;
}
}
else
{
lean_dec_ref(v_e_957_);
lean_dec_ref(v_varNames_956_);
return v___x_966_;
}
}
else
{
lean_object* v___x_977_; uint8_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
lean_dec_ref(v_varNames_956_);
v___x_977_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_978_ = 0;
v___x_979_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_980_ = l_Lean_mkLambda(v___x_977_, v___x_978_, v___x_979_, v_e_957_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___boxed(lean_object* v_varNames_982_, lean_object* v_e_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_varNames_982_, v_e_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
return v_res_989_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_dummy_995_; 
v___x_993_ = lean_box(0);
v___x_994_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_packType___closed__1));
v_dummy_995_ = l_Lean_Expr_const___override(v___x_994_, v___x_993_);
return v_dummy_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(lean_object* v_args_996_, lean_object* v_type_997_, lean_object* v_packedDomain_998_, lean_object* v_tail_999_, lean_object* v_x_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_dummy_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_dummy_1006_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1000_);
v___x_1007_ = lean_array_push(v_args_996_, v_x_1000_);
v___x_1008_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_997_, v_packedDomain_998_, v_dummy_1006_, v___x_1007_, v_tail_999_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; uint8_t v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1008_);
v___x_1010_ = lean_unsigned_to_nat(1u);
v___x_1011_ = lean_mk_empty_array_with_capacity(v___x_1010_);
v___x_1012_ = lean_array_push(v___x_1011_, v_x_1000_);
v___x_1013_ = 0;
v___x_1014_ = 1;
v___x_1015_ = 1;
v___x_1016_ = l_Lean_Meta_mkForallFVars(v___x_1012_, v_a_1009_, v___x_1013_, v___x_1014_, v___x_1014_, v___x_1015_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec_ref(v___x_1012_);
return v___x_1016_;
}
else
{
lean_dec_ref(v_x_1000_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed(lean_object* v_args_1017_, lean_object* v_type_1018_, lean_object* v_packedDomain_1019_, lean_object* v_tail_1020_, lean_object* v_x_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(v_args_1017_, v_type_1018_, v_packedDomain_1019_, v_tail_1020_, v_x_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed(lean_object* v_arg_1028_, lean_object* v_args_1029_, lean_object* v_type_1030_, lean_object* v_packedDomain_1031_, lean_object* v_tail_1032_, lean_object* v___x_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v___x_927__boxed_1040_; lean_object* v_res_1041_; 
v___x_927__boxed_1040_ = lean_unbox(v___x_1033_);
v_res_1041_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(v_arg_1028_, v_args_1029_, v_type_1030_, v_packedDomain_1031_, v_tail_1032_, v___x_927__boxed_1040_, v_x_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(lean_object* v_type_1042_, lean_object* v_packedDomain_1043_, lean_object* v_domain_1044_, lean_object* v_args_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; 
if (lean_obj_tag(v_a_1046_) == 0)
{
lean_object* v_packedArg_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec_ref(v_domain_1044_);
v_packedArg_1061_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_1043_, v_args_1045_);
lean_dec_ref(v_args_1045_);
lean_dec_ref(v_packedDomain_1043_);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_mk_empty_array_with_capacity(v___x_1062_);
v___x_1064_ = lean_array_push(v___x_1063_, v_packedArg_1061_);
v___x_1065_ = l_Lean_Meta_instantiateForall(v_type_1042_, v___x_1064_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
lean_dec_ref(v___x_1064_);
return v___x_1065_;
}
else
{
lean_object* v_tail_1066_; 
v_tail_1066_ = lean_ctor_get(v_a_1046_, 1);
lean_inc(v_tail_1066_);
if (lean_obj_tag(v_tail_1066_) == 0)
{
lean_object* v_head_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; 
v_head_1067_ = lean_ctor_get(v_a_1046_, 0);
lean_inc(v_head_1067_);
lean_dec_ref(v_a_1046_);
v___f_1068_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1068_, 0, v_args_1045_);
lean_closure_set(v___f_1068_, 1, v_type_1042_);
lean_closure_set(v___f_1068_, 2, v_packedDomain_1043_);
lean_closure_set(v___f_1068_, 3, v_tail_1066_);
v___x_1069_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1067_, v_domain_1044_, v___f_1068_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
return v___x_1069_;
}
else
{
lean_object* v_head_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_head_1070_ = lean_ctor_get(v_a_1046_, 0);
lean_inc(v_head_1070_);
lean_dec_ref(v_a_1046_);
lean_inc_ref(v_domain_1044_);
v___x_1071_ = l_Lean_Expr_cleanupAnnotations(v_domain_1044_);
v___x_1072_ = l_Lean_Expr_isApp(v___x_1071_);
if (v___x_1072_ == 0)
{
lean_dec_ref(v___x_1071_);
lean_dec(v_head_1070_);
lean_dec(v_tail_1066_);
lean_dec_ref(v_args_1045_);
lean_dec_ref(v_packedDomain_1043_);
lean_dec_ref(v_type_1042_);
v___y_1053_ = v_a_1047_;
v___y_1054_ = v_a_1048_;
v___y_1055_ = v_a_1049_;
v___y_1056_ = v_a_1050_;
goto v___jp_1052_;
}
else
{
lean_object* v_arg_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v_arg_1073_ = lean_ctor_get(v___x_1071_, 1);
lean_inc_ref(v_arg_1073_);
v___x_1074_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1071_);
v___x_1075_ = l_Lean_Expr_isApp(v___x_1074_);
if (v___x_1075_ == 0)
{
lean_dec_ref(v___x_1074_);
lean_dec_ref(v_arg_1073_);
lean_dec(v_head_1070_);
lean_dec(v_tail_1066_);
lean_dec_ref(v_args_1045_);
lean_dec_ref(v_packedDomain_1043_);
lean_dec_ref(v_type_1042_);
v___y_1053_ = v_a_1047_;
v___y_1054_ = v_a_1048_;
v___y_1055_ = v_a_1049_;
v___y_1056_ = v_a_1050_;
goto v___jp_1052_;
}
else
{
lean_object* v_arg_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_arg_1076_ = lean_ctor_get(v___x_1074_, 1);
lean_inc_ref(v_arg_1076_);
v___x_1077_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1074_);
v___x_1078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1079_ = l_Lean_Expr_isConstOf(v___x_1077_, v___x_1078_);
lean_dec_ref(v___x_1077_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v_arg_1076_);
lean_dec_ref(v_arg_1073_);
lean_dec(v_head_1070_);
lean_dec(v_tail_1066_);
lean_dec_ref(v_args_1045_);
lean_dec_ref(v_packedDomain_1043_);
lean_dec_ref(v_type_1042_);
v___y_1053_ = v_a_1047_;
v___y_1054_ = v_a_1048_;
v___y_1055_ = v_a_1049_;
v___y_1056_ = v_a_1050_;
goto v___jp_1052_;
}
else
{
lean_object* v___x_1080_; lean_object* v___f_1081_; lean_object* v___x_1082_; 
lean_dec_ref(v_domain_1044_);
v___x_1080_ = lean_box(v___x_1079_);
v___f_1081_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1081_, 0, v_arg_1073_);
lean_closure_set(v___f_1081_, 1, v_args_1045_);
lean_closure_set(v___f_1081_, 2, v_type_1042_);
lean_closure_set(v___f_1081_, 3, v_packedDomain_1043_);
lean_closure_set(v___f_1081_, 4, v_tail_1066_);
lean_closure_set(v___f_1081_, 5, v___x_1080_);
v___x_1082_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1070_, v_arg_1076_, v___f_1081_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
return v___x_1082_;
}
}
}
}
}
v___jp_1052_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1057_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1);
v___x_1058_ = l_Lean_MessageData_ofExpr(v_domain_1044_);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1059_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(lean_object* v_arg_1083_, lean_object* v_args_1084_, lean_object* v_type_1085_, lean_object* v_packedDomain_1086_, lean_object* v_tail_1087_, uint8_t v___x_1088_, lean_object* v_x_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1095_ = lean_unsigned_to_nat(1u);
v___x_1096_ = lean_mk_empty_array_with_capacity(v___x_1095_);
lean_inc_ref(v_x_1089_);
v___x_1097_ = lean_array_push(v___x_1096_, v_x_1089_);
lean_inc_ref(v___x_1097_);
v___x_1098_ = l_Lean_Expr_beta(v_arg_1083_, v___x_1097_);
v___x_1099_ = lean_array_push(v_args_1084_, v_x_1089_);
v___x_1100_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1085_, v_packedDomain_1086_, v___x_1098_, v___x_1099_, v_tail_1087_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; uint8_t v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref(v___x_1100_);
v___x_1102_ = 0;
v___x_1103_ = 1;
v___x_1104_ = l_Lean_Meta_mkForallFVars(v___x_1097_, v_a_1101_, v___x_1102_, v___x_1088_, v___x_1088_, v___x_1103_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec_ref(v___x_1097_);
return v___x_1104_;
}
else
{
lean_dec_ref(v___x_1097_);
return v___x_1100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___boxed(lean_object* v_type_1105_, lean_object* v_packedDomain_1106_, lean_object* v_domain_1107_, lean_object* v_args_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1105_, v_packedDomain_1106_, v_domain_1107_, v_args_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
return v_res_1115_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0));
v___x_1118_ = l_Lean_stringToMessageData(v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(lean_object* v_varNames_1119_, lean_object* v_type_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; uint8_t v___x_1135_; 
v___x_1135_ = l_Lean_Expr_isForall(v_type_1120_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v_varNames_1119_);
v___x_1136_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_1137_ = l_Lean_MessageData_ofExpr(v_type_1120_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1138_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
v___y_1127_ = v_a_1121_;
v___y_1128_ = v_a_1122_;
v___y_1129_ = v_a_1123_;
v___y_1130_ = v_a_1124_;
goto v___jp_1126_;
}
v___jp_1126_:
{
lean_object* v_packedDomain_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_packedDomain_1131_ = l_Lean_Expr_bindingDomain_x21(v_type_1120_);
v___x_1132_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_1133_ = lean_array_to_list(v_varNames_1119_);
lean_inc_ref(v_packedDomain_1131_);
v___x_1134_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1120_, v_packedDomain_1131_, v_packedDomain_1131_, v___x_1132_, v___x_1133_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___boxed(lean_object* v_varNames_1148_, lean_object* v_type_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_varNames_1148_, v_type_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
return v_res_1155_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0));
v___x_1158_ = l_Lean_stringToMessageData(v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(lean_object* v_args_1159_, lean_object* v_e_1160_, lean_object* v_packedDomain_1161_, lean_object* v_tail_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_dummy_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_dummy_1169_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1163_);
v___x_1170_ = lean_array_push(v_args_1159_, v_x_1163_);
v___x_1171_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1160_, v_packedDomain_1161_, v_dummy_1169_, v___x_1170_, v_tail_1162_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; uint8_t v___x_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref(v___x_1171_);
v___x_1173_ = lean_unsigned_to_nat(1u);
v___x_1174_ = lean_mk_empty_array_with_capacity(v___x_1173_);
v___x_1175_ = lean_array_push(v___x_1174_, v_x_1163_);
v___x_1176_ = 0;
v___x_1177_ = 1;
v___x_1178_ = 1;
v___x_1179_ = l_Lean_Meta_mkLambdaFVars(v___x_1175_, v_a_1172_, v___x_1176_, v___x_1177_, v___x_1176_, v___x_1177_, v___x_1178_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec_ref(v___x_1175_);
return v___x_1179_;
}
else
{
lean_dec_ref(v_x_1163_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed(lean_object* v_args_1180_, lean_object* v_e_1181_, lean_object* v_packedDomain_1182_, lean_object* v_tail_1183_, lean_object* v_x_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(v_args_1180_, v_e_1181_, v_packedDomain_1182_, v_tail_1183_, v_x_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed(lean_object* v_arg_1191_, lean_object* v_args_1192_, lean_object* v_e_1193_, lean_object* v_packedDomain_1194_, lean_object* v_tail_1195_, lean_object* v___x_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
uint8_t v___x_1045__boxed_1203_; lean_object* v_res_1204_; 
v___x_1045__boxed_1203_ = lean_unbox(v___x_1196_);
v_res_1204_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(v_arg_1191_, v_args_1192_, v_e_1193_, v_packedDomain_1194_, v_tail_1195_, v___x_1045__boxed_1203_, v_x_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(lean_object* v_e_1205_, lean_object* v_packedDomain_1206_, lean_object* v_domain_1207_, lean_object* v_args_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; 
if (lean_obj_tag(v_a_1209_) == 0)
{
lean_object* v_packedArg_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v_domain_1207_);
v_packedArg_1224_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_1206_, v_args_1208_);
lean_dec_ref(v_args_1208_);
lean_dec_ref(v_packedDomain_1206_);
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = lean_mk_empty_array_with_capacity(v___x_1225_);
v___x_1227_ = lean_array_push(v___x_1226_, v_packedArg_1224_);
v___x_1228_ = l_Lean_Expr_beta(v_e_1205_, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
else
{
lean_object* v_tail_1230_; 
v_tail_1230_ = lean_ctor_get(v_a_1209_, 1);
lean_inc(v_tail_1230_);
if (lean_obj_tag(v_tail_1230_) == 0)
{
lean_object* v_head_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; 
v_head_1231_ = lean_ctor_get(v_a_1209_, 0);
lean_inc(v_head_1231_);
lean_dec_ref(v_a_1209_);
v___f_1232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1232_, 0, v_args_1208_);
lean_closure_set(v___f_1232_, 1, v_e_1205_);
lean_closure_set(v___f_1232_, 2, v_packedDomain_1206_);
lean_closure_set(v___f_1232_, 3, v_tail_1230_);
v___x_1233_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1231_, v_domain_1207_, v___f_1232_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
return v___x_1233_;
}
else
{
lean_object* v_head_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_head_1234_ = lean_ctor_get(v_a_1209_, 0);
lean_inc(v_head_1234_);
lean_dec_ref(v_a_1209_);
lean_inc_ref(v_domain_1207_);
v___x_1235_ = l_Lean_Expr_cleanupAnnotations(v_domain_1207_);
v___x_1236_ = l_Lean_Expr_isApp(v___x_1235_);
if (v___x_1236_ == 0)
{
lean_dec_ref(v___x_1235_);
lean_dec(v_head_1234_);
lean_dec(v_tail_1230_);
lean_dec_ref(v_args_1208_);
lean_dec_ref(v_packedDomain_1206_);
lean_dec_ref(v_e_1205_);
v___y_1216_ = v_a_1210_;
v___y_1217_ = v_a_1211_;
v___y_1218_ = v_a_1212_;
v___y_1219_ = v_a_1213_;
goto v___jp_1215_;
}
else
{
lean_object* v_arg_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_arg_1237_ = lean_ctor_get(v___x_1235_, 1);
lean_inc_ref(v_arg_1237_);
v___x_1238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1235_);
v___x_1239_ = l_Lean_Expr_isApp(v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_arg_1237_);
lean_dec(v_head_1234_);
lean_dec(v_tail_1230_);
lean_dec_ref(v_args_1208_);
lean_dec_ref(v_packedDomain_1206_);
lean_dec_ref(v_e_1205_);
v___y_1216_ = v_a_1210_;
v___y_1217_ = v_a_1211_;
v___y_1218_ = v_a_1212_;
v___y_1219_ = v_a_1213_;
goto v___jp_1215_;
}
else
{
lean_object* v_arg_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_arg_1240_ = lean_ctor_get(v___x_1238_, 1);
lean_inc_ref(v_arg_1240_);
v___x_1241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1238_);
v___x_1242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1243_ = l_Lean_Expr_isConstOf(v___x_1241_, v___x_1242_);
lean_dec_ref(v___x_1241_);
if (v___x_1243_ == 0)
{
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1237_);
lean_dec(v_head_1234_);
lean_dec(v_tail_1230_);
lean_dec_ref(v_args_1208_);
lean_dec_ref(v_packedDomain_1206_);
lean_dec_ref(v_e_1205_);
v___y_1216_ = v_a_1210_;
v___y_1217_ = v_a_1211_;
v___y_1218_ = v_a_1212_;
v___y_1219_ = v_a_1213_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1244_; lean_object* v___f_1245_; lean_object* v___x_1246_; 
lean_dec_ref(v_domain_1207_);
v___x_1244_ = lean_box(v___x_1243_);
v___f_1245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1245_, 0, v_arg_1237_);
lean_closure_set(v___f_1245_, 1, v_args_1208_);
lean_closure_set(v___f_1245_, 2, v_e_1205_);
lean_closure_set(v___f_1245_, 3, v_packedDomain_1206_);
lean_closure_set(v___f_1245_, 4, v_tail_1230_);
lean_closure_set(v___f_1245_, 5, v___x_1244_);
v___x_1246_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1234_, v_arg_1240_, v___f_1245_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
return v___x_1246_;
}
}
}
}
}
v___jp_1215_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1220_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1);
v___x_1221_ = l_Lean_MessageData_ofExpr(v_domain_1207_);
v___x_1222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1222_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(lean_object* v_arg_1247_, lean_object* v_args_1248_, lean_object* v_e_1249_, lean_object* v_packedDomain_1250_, lean_object* v_tail_1251_, uint8_t v___x_1252_, lean_object* v_x_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_mk_empty_array_with_capacity(v___x_1259_);
lean_inc_ref(v_x_1253_);
v___x_1261_ = lean_array_push(v___x_1260_, v_x_1253_);
lean_inc_ref(v___x_1261_);
v___x_1262_ = l_Lean_Expr_beta(v_arg_1247_, v___x_1261_);
v___x_1263_ = lean_array_push(v_args_1248_, v_x_1253_);
v___x_1264_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1249_, v_packedDomain_1250_, v___x_1262_, v___x_1263_, v_tail_1251_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; uint8_t v___x_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref(v___x_1264_);
v___x_1266_ = 0;
v___x_1267_ = 1;
v___x_1268_ = l_Lean_Meta_mkLambdaFVars(v___x_1261_, v_a_1265_, v___x_1266_, v___x_1252_, v___x_1266_, v___x_1252_, v___x_1267_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec_ref(v___x_1261_);
return v___x_1268_;
}
else
{
lean_dec_ref(v___x_1261_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___boxed(lean_object* v_e_1269_, lean_object* v_packedDomain_1270_, lean_object* v_domain_1271_, lean_object* v_args_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1269_, v_packedDomain_1270_, v_domain_1271_, v_args_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
return v_res_1279_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0));
v___x_1282_ = l_Lean_stringToMessageData(v___x_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1283_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_pack___closed__2, &l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2);
v___x_1284_ = lean_unsigned_to_nat(1u);
v___x_1285_ = lean_mk_empty_array_with_capacity(v___x_1284_);
v___x_1286_ = lean_array_push(v___x_1285_, v___x_1283_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(lean_object* v_varNames_1287_, lean_object* v_e_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1294_ = lean_array_get_size(v_varNames_1287_);
v___x_1295_ = lean_unsigned_to_nat(0u);
v___x_1296_ = lean_nat_dec_eq(v___x_1294_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
lean_inc(v_a_1292_);
lean_inc_ref(v_a_1291_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc_ref(v_e_1288_);
v___x_1297_ = lean_infer_type(v_e_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1299_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1297_);
v___x_1299_ = l_Lean_Meta_whnfForall(v_a_1298_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; uint8_t v___x_1310_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref(v___x_1299_);
v___x_1310_ = l_Lean_Expr_isForall(v_a_1300_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_e_1288_);
lean_dec_ref(v_varNames_1287_);
v___x_1311_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1);
v___x_1312_ = l_Lean_MessageData_ofExpr(v_a_1300_);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1313_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
else
{
v___y_1302_ = v_a_1289_;
v___y_1303_ = v_a_1290_;
v___y_1304_ = v_a_1291_;
v___y_1305_ = v_a_1292_;
goto v___jp_1301_;
}
v___jp_1301_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1306_ = l_Lean_Expr_bindingDomain_x21(v_a_1300_);
lean_dec(v_a_1300_);
v___x_1307_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_1308_ = lean_array_to_list(v_varNames_1287_);
lean_inc_ref(v___x_1306_);
v___x_1309_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1288_, v___x_1306_, v___x_1306_, v___x_1307_, v___x_1308_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1309_;
}
}
else
{
lean_dec_ref(v_e_1288_);
lean_dec_ref(v_varNames_1287_);
return v___x_1299_;
}
}
else
{
lean_dec_ref(v_e_1288_);
lean_dec_ref(v_varNames_1287_);
return v___x_1297_;
}
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec_ref(v_varNames_1287_);
v___x_1323_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2);
v___x_1324_ = l_Lean_Expr_beta(v_e_1288_, v___x_1323_);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___boxed(lean_object* v_varNames_1326_, lean_object* v_e_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v_varNames_1326_, v_e_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(lean_object* v_as_1337_, size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_b_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
uint8_t v___x_1346_; 
v___x_1346_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v_b_1340_);
return v___x_1347_;
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_a_1348_ = lean_array_uget_borrowed(v_as_1337_, v_i_1339_);
v___x_1349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1350_ = lean_unsigned_to_nat(2u);
v___x_1351_ = lean_mk_empty_array_with_capacity(v___x_1350_);
lean_inc(v_a_1348_);
v___x_1352_ = lean_array_push(v___x_1351_, v_a_1348_);
v___x_1353_ = lean_array_push(v___x_1352_, v_b_1340_);
v___x_1354_ = l_Lean_Meta_mkAppM(v___x_1349_, v___x_1353_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; size_t v___x_1356_; size_t v___x_1357_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_add(v_i_1339_, v___x_1356_);
v_i_1339_ = v___x_1357_;
v_b_1340_ = v_a_1355_;
goto _start;
}
else
{
return v___x_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___boxed(lean_object* v_as_1359_, lean_object* v_sz_1360_, lean_object* v_i_1361_, lean_object* v_b_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
size_t v_sz_boxed_1368_; size_t v_i_boxed_1369_; lean_object* v_res_1370_; 
v_sz_boxed_1368_ = lean_unbox_usize(v_sz_1360_);
lean_dec(v_sz_1360_);
v_i_boxed_1369_ = lean_unbox_usize(v_i_1361_);
lean_dec(v_i_1361_);
v_res_1370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v_as_1359_, v_sz_boxed_1368_, v_i_boxed_1369_, v_b_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec_ref(v_as_1359_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType(lean_object* v_ds_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_r_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; size_t v_sz_1384_; size_t v___x_1385_; lean_object* v___x_1386_; 
v___x_1377_ = l_Lean_instInhabitedExpr;
v___x_1378_ = lean_array_get_size(v_ds_1371_);
v___x_1379_ = lean_unsigned_to_nat(1u);
v___x_1380_ = lean_nat_sub(v___x_1378_, v___x_1379_);
v_r_1381_ = lean_array_get(v___x_1377_, v_ds_1371_, v___x_1380_);
lean_dec(v___x_1380_);
v___x_1382_ = lean_array_pop(v_ds_1371_);
v___x_1383_ = l_Array_reverse___redArg(v___x_1382_);
v_sz_1384_ = lean_array_size(v___x_1383_);
v___x_1385_ = ((size_t)0ULL);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v___x_1383_, v_sz_1384_, v___x_1385_, v_r_1381_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
lean_dec_ref(v___x_1383_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType___boxed(lean_object* v_ds_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v_ds_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
return v_res_1393_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0));
v___x_1396_ = l_Lean_stringToMessageData(v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(lean_object* v_n_1397_, lean_object* v_type_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v_zero_1413_; uint8_t v_isZero_1414_; 
v_zero_1413_ = lean_unsigned_to_nat(0u);
v_isZero_1414_ = lean_nat_dec_eq(v_n_1397_, v_zero_1413_);
if (v_isZero_1414_ == 1)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec_ref(v_type_1398_);
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
else
{
lean_object* v_one_1417_; lean_object* v_n_1418_; uint8_t v___x_1419_; 
v_one_1417_ = lean_unsigned_to_nat(1u);
v_n_1418_ = lean_nat_sub(v_n_1397_, v_one_1417_);
v___x_1419_ = lean_nat_dec_eq(v_n_1418_, v_zero_1413_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; uint8_t v___x_1421_; 
lean_inc_ref(v_type_1398_);
v___x_1420_ = l_Lean_Expr_cleanupAnnotations(v_type_1398_);
v___x_1421_ = l_Lean_Expr_isApp(v___x_1420_);
if (v___x_1421_ == 0)
{
lean_dec_ref(v___x_1420_);
lean_dec(v_n_1418_);
v___y_1405_ = v_a_1399_;
v___y_1406_ = v_a_1400_;
v___y_1407_ = v_a_1401_;
v___y_1408_ = v_a_1402_;
goto v___jp_1404_;
}
else
{
lean_object* v_arg_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v_arg_1422_ = lean_ctor_get(v___x_1420_, 1);
lean_inc_ref(v_arg_1422_);
v___x_1423_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1420_);
v___x_1424_ = l_Lean_Expr_isApp(v___x_1423_);
if (v___x_1424_ == 0)
{
lean_dec_ref(v___x_1423_);
lean_dec_ref(v_arg_1422_);
lean_dec(v_n_1418_);
v___y_1405_ = v_a_1399_;
v___y_1406_ = v_a_1400_;
v___y_1407_ = v_a_1401_;
v___y_1408_ = v_a_1402_;
goto v___jp_1404_;
}
else
{
lean_object* v_arg_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_arg_1425_ = lean_ctor_get(v___x_1423_, 1);
lean_inc_ref(v_arg_1425_);
v___x_1426_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1423_);
v___x_1427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1428_ = l_Lean_Expr_isConstOf(v___x_1426_, v___x_1427_);
lean_dec_ref(v___x_1426_);
if (v___x_1428_ == 0)
{
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1422_);
lean_dec(v_n_1418_);
v___y_1405_ = v_a_1399_;
v___y_1406_ = v_a_1400_;
v___y_1407_ = v_a_1401_;
v___y_1408_ = v_a_1402_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1429_; 
lean_dec_ref(v_type_1398_);
v___x_1429_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1418_, v_arg_1422_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_n_1418_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1438_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_arg_1425_);
lean_ctor_set(v___x_1434_, 1, v_a_1430_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1434_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
else
{
lean_dec_ref(v_arg_1425_);
return v___x_1429_;
}
}
}
}
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec(v_n_1418_);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1440_, 0, v_type_1398_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
}
v___jp_1404_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1);
v___x_1410_ = l_Lean_MessageData_ofExpr(v_type_1398_);
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1409_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1411_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___boxed(lean_object* v_n_1442_, lean_object* v_type_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1442_, v_type_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_n_1442_);
return v_res_1449_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0(void){
_start:
{
lean_object* v___x_1450_; lean_object* v_dummy_1451_; 
v___x_1450_ = lean_box(0);
v_dummy_1451_ = l_Lean_Expr_sort___override(v___x_1450_);
return v_dummy_1451_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1454_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1));
v___x_1455_ = lean_unsigned_to_nat(8u);
v___x_1456_ = lean_unsigned_to_nat(276u);
v___x_1457_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0));
v___x_1458_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1459_ = l_mkPanicMessageWithDecl(v___x_1458_, v___x_1457_, v___x_1456_, v___x_1455_, v___x_1454_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(lean_object* v_i_1468_, lean_object* v_fidx_1469_, lean_object* v_numFuncs_1470_, lean_object* v_arg_1471_, lean_object* v_x_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_x_1472_) == 5)
{
lean_object* v_fn_1481_; lean_object* v_arg_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_fn_1481_ = lean_ctor_get(v_x_1472_, 0);
lean_inc_ref(v_fn_1481_);
v_arg_1482_ = lean_ctor_get(v_x_1472_, 1);
lean_inc_ref(v_arg_1482_);
lean_dec_ref(v_x_1472_);
v___x_1483_ = lean_array_set(v_x_1473_, v_x_1474_, v_arg_1482_);
v___x_1484_ = lean_nat_sub(v_x_1474_, v___x_1480_);
lean_dec(v_x_1474_);
v_x_1472_ = v_fn_1481_;
v_x_1473_ = v___x_1483_;
v_x_1474_ = v___x_1484_;
goto _start;
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
lean_dec(v_x_1474_);
v___x_1486_ = lean_array_get_size(v_x_1473_);
v___x_1487_ = lean_unsigned_to_nat(2u);
v___x_1488_ = lean_nat_dec_eq(v___x_1486_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec_ref(v_x_1473_);
lean_dec_ref(v_x_1472_);
lean_dec_ref(v_arg_1471_);
v___x_1489_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2);
v___x_1490_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1489_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
return v___x_1490_;
}
else
{
uint8_t v___x_1491_; 
v___x_1491_ = lean_nat_dec_eq(v_i_1468_, v_fidx_1469_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1492_ = lean_nat_add(v_i_1468_, v___x_1480_);
v___x_1493_ = l_Lean_instInhabitedExpr;
v___x_1494_ = lean_array_get(v___x_1493_, v_x_1473_, v___x_1480_);
lean_inc(v___x_1494_);
v___x_1495_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1470_, v_fidx_1469_, v_arg_1471_, v___x_1492_, v___x_1494_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___x_1492_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1509_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1509_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1509_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1500_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1501_ = l_Lean_Expr_constLevels_x21(v_x_1472_);
lean_dec_ref(v_x_1472_);
v___x_1502_ = l_Lean_mkConst(v___x_1500_, v___x_1501_);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_array_get(v___x_1493_, v_x_1473_, v___x_1503_);
lean_dec_ref(v_x_1473_);
v___x_1505_ = l_Lean_mkApp3(v___x_1502_, v___x_1504_, v___x_1494_, v_a_1496_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1505_);
v___x_1507_ = v___x_1498_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
else
{
lean_dec(v___x_1494_);
lean_dec_ref(v_x_1473_);
lean_dec_ref(v_x_1472_);
return v___x_1495_;
}
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1510_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1511_ = l_Lean_Expr_constLevels_x21(v_x_1472_);
lean_dec_ref(v_x_1472_);
v___x_1512_ = l_Lean_mkConst(v___x_1510_, v___x_1511_);
v___x_1513_ = l_Lean_instInhabitedExpr;
v___x_1514_ = lean_unsigned_to_nat(0u);
v___x_1515_ = lean_array_get(v___x_1513_, v_x_1473_, v___x_1514_);
v___x_1516_ = lean_array_get(v___x_1513_, v_x_1473_, v___x_1480_);
lean_dec_ref(v_x_1473_);
v___x_1517_ = l_Lean_mkApp3(v___x_1512_, v___x_1515_, v___x_1516_, v_arg_1471_);
v___x_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
return v___x_1518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(lean_object* v_numFuncs_1519_, lean_object* v_fidx_1520_, lean_object* v_arg_1521_, lean_object* v_i_1522_, lean_object* v_type_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = lean_unsigned_to_nat(1u);
v___x_1530_ = lean_nat_sub(v_numFuncs_1519_, v___x_1529_);
v___x_1531_ = lean_nat_dec_le(v___x_1530_, v_i_1522_);
lean_dec(v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_Meta_whnfD(v_type_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v_dummy_1534_; lean_object* v_nargs_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v___x_1532_);
v_dummy_1534_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
v_nargs_1535_ = l_Lean_Expr_getAppNumArgs(v_a_1533_);
lean_inc(v_nargs_1535_);
v___x_1536_ = lean_mk_array(v_nargs_1535_, v_dummy_1534_);
v___x_1537_ = lean_nat_sub(v_nargs_1535_, v___x_1529_);
lean_dec(v_nargs_1535_);
v___x_1538_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1522_, v_fidx_1520_, v_numFuncs_1519_, v_arg_1521_, v_a_1533_, v___x_1536_, v___x_1537_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
return v___x_1538_;
}
else
{
lean_dec_ref(v_arg_1521_);
return v___x_1532_;
}
}
else
{
lean_object* v___x_1539_; 
lean_dec_ref(v_type_1523_);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v_arg_1521_);
return v___x_1539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___boxed(lean_object* v_numFuncs_1540_, lean_object* v_fidx_1541_, lean_object* v_arg_1542_, lean_object* v_i_1543_, lean_object* v_type_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1540_, v_fidx_1541_, v_arg_1542_, v_i_1543_, v_type_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_i_1543_);
lean_dec(v_fidx_1541_);
lean_dec(v_numFuncs_1540_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___boxed(lean_object* v_i_1551_, lean_object* v_fidx_1552_, lean_object* v_numFuncs_1553_, lean_object* v_arg_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_, lean_object* v_x_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1551_, v_fidx_1552_, v_numFuncs_1553_, v_arg_1554_, v_x_1555_, v_x_1556_, v_x_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v_numFuncs_1553_);
lean_dec(v_fidx_1552_);
lean_dec(v_i_1551_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack(lean_object* v_numFuncs_1564_, lean_object* v_domain_1565_, lean_object* v_fidx_1566_, lean_object* v_arg_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1564_, v_fidx_1566_, v_arg_1567_, v___x_1573_, v_domain_1565_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack___boxed(lean_object* v_numFuncs_1575_, lean_object* v_domain_1576_, lean_object* v_fidx_1577_, lean_object* v_arg_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v_numFuncs_1575_, v_domain_1576_, v_fidx_1577_, v_arg_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_fidx_1577_);
lean_dec(v_numFuncs_1575_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(lean_object* v_numFuncs_1585_, lean_object* v_b_1586_){
_start:
{
lean_object* v_fst_1587_; lean_object* v_snd_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1623_; 
v_fst_1587_ = lean_ctor_get(v_b_1586_, 0);
v_snd_1588_ = lean_ctor_get(v_b_1586_, 1);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_b_1586_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1590_ = v_b_1586_;
v_isShared_1591_ = v_isSharedCheck_1623_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_snd_1588_);
lean_inc(v_fst_1587_);
lean_dec(v_b_1586_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1623_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v_funidx_1593_; uint8_t v___x_1594_; 
v___x_1592_ = lean_unsigned_to_nat(1u);
v_funidx_1593_ = lean_nat_add(v_fst_1587_, v___x_1592_);
v___x_1594_ = lean_nat_dec_lt(v_funidx_1593_, v_numFuncs_1585_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1596_; 
lean_dec(v_funidx_1593_);
if (v_isShared_1591_ == 0)
{
v___x_1596_ = v___x_1590_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_fst_1587_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_snd_1588_);
v___x_1596_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
return v___x_1597_;
}
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1599_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1600_ = lean_unsigned_to_nat(3u);
v___x_1601_ = l_Lean_Expr_isAppOfArity(v_snd_1588_, v___x_1599_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
lean_dec(v_funidx_1593_);
v___x_1602_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1603_ = l_Lean_Expr_isAppOfArity(v_snd_1588_, v___x_1602_, v___x_1600_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_del_object(v___x_1590_);
lean_dec(v_snd_1588_);
lean_dec(v_fst_1587_);
v___x_1604_ = lean_box(0);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v_e_1609_; lean_object* v___x_1611_; 
v___x_1605_ = lean_unsigned_to_nat(2u);
v___x_1606_ = l_Lean_Expr_getAppNumArgs(v_snd_1588_);
v___x_1607_ = lean_nat_sub(v___x_1606_, v___x_1605_);
lean_dec(v___x_1606_);
v___x_1608_ = lean_nat_sub(v___x_1607_, v___x_1592_);
lean_dec(v___x_1607_);
v_e_1609_ = l_Lean_Expr_getRevArg_x21(v_snd_1588_, v___x_1608_);
lean_dec(v_snd_1588_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 1, v_e_1609_);
v___x_1611_ = v___x_1590_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_fst_1587_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_e_1609_);
v___x_1611_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
return v___x_1612_;
}
}
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v_e_1618_; lean_object* v___x_1620_; 
lean_dec(v_fst_1587_);
v___x_1614_ = lean_unsigned_to_nat(2u);
v___x_1615_ = l_Lean_Expr_getAppNumArgs(v_snd_1588_);
v___x_1616_ = lean_nat_sub(v___x_1615_, v___x_1614_);
lean_dec(v___x_1615_);
v___x_1617_ = lean_nat_sub(v___x_1616_, v___x_1592_);
lean_dec(v___x_1616_);
v_e_1618_ = l_Lean_Expr_getRevArg_x21(v_snd_1588_, v___x_1617_);
lean_dec(v_snd_1588_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 1, v_e_1618_);
lean_ctor_set(v___x_1590_, 0, v_funidx_1593_);
v___x_1620_ = v___x_1590_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_funidx_1593_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_e_1618_);
v___x_1620_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
v_b_1586_ = v___x_1620_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___boxed(lean_object* v_numFuncs_1624_, lean_object* v_b_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(v_numFuncs_1624_, v_b_1625_);
lean_dec(v_numFuncs_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack(lean_object* v_numFuncs_1627_, lean_object* v_expr_1628_){
_start:
{
lean_object* v_funidx_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v_funidx_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v_funidx_1629_);
lean_ctor_set(v___x_1630_, 1, v_expr_1628_);
v___x_1631_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(v_numFuncs_1627_, v___x_1630_);
if (lean_obj_tag(v___x_1631_) == 0)
{
return v___x_1631_;
}
else
{
lean_object* v_val_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1648_; 
v_val_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1648_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_val_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1648_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v_fst_1636_; lean_object* v_snd_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1647_; 
v_fst_1636_ = lean_ctor_get(v_val_1632_, 0);
v_snd_1637_ = lean_ctor_get(v_val_1632_, 1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_val_1632_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1639_ = v_val_1632_;
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_snd_1637_);
lean_inc(v_fst_1636_);
lean_dec(v_val_1632_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_fst_1636_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_snd_1637_);
v___x_1642_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1644_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1642_);
v___x_1644_ = v___x_1634_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack___boxed(lean_object* v_numFuncs_1649_, lean_object* v_expr_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v_numFuncs_1649_, v_expr_1650_);
lean_dec(v_numFuncs_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(lean_object* v___x_1652_, lean_object* v___x_1653_, lean_object* v_types_1654_, lean_object* v_i_1655_, uint8_t v___x_1656_, uint8_t v___x_1657_, uint8_t v___x_1658_, lean_object* v_x_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_inc_ref(v_x_1659_);
v___x_1665_ = lean_array_push(v___x_1652_, v_x_1659_);
v___x_1666_ = lean_array_get_borrowed(v___x_1653_, v_types_1654_, v_i_1655_);
v___x_1667_ = l_Lean_Expr_bindingBody_x21(v___x_1666_);
v___x_1668_ = lean_expr_instantiate1(v___x_1667_, v_x_1659_);
lean_dec_ref(v_x_1659_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = l_Lean_Meta_mkLambdaFVars(v___x_1665_, v___x_1668_, v___x_1656_, v___x_1657_, v___x_1656_, v___x_1657_, v___x_1658_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec_ref(v___x_1665_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(lean_object* v___x_1670_, lean_object* v___x_1671_, lean_object* v_types_1672_, lean_object* v_i_1673_, lean_object* v___x_1674_, lean_object* v___x_1675_, lean_object* v___x_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v___x_1974__boxed_1683_; uint8_t v___x_1975__boxed_1684_; uint8_t v___x_1976__boxed_1685_; lean_object* v_res_1686_; 
v___x_1974__boxed_1683_ = lean_unbox(v___x_1674_);
v___x_1975__boxed_1684_ = lean_unbox(v___x_1675_);
v___x_1976__boxed_1685_ = lean_unbox(v___x_1676_);
v_res_1686_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(v___x_1670_, v___x_1671_, v_types_1672_, v_i_1673_, v___x_1974__boxed_1683_, v___x_1975__boxed_1684_, v___x_1976__boxed_1685_, v_x_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v_i_1673_);
lean_dec_ref(v_types_1672_);
lean_dec_ref(v___x_1671_);
return v_res_1686_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1689_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1));
v___x_1690_ = lean_unsigned_to_nat(6u);
v___x_1691_ = lean_unsigned_to_nat(318u);
v___x_1692_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0));
v___x_1693_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1694_ = l_mkPanicMessageWithDecl(v___x_1693_, v___x_1692_, v___x_1691_, v___x_1690_, v___x_1689_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object* v_i_1695_, lean_object* v___x_1696_, lean_object* v_types_1697_, lean_object* v_u_1698_, lean_object* v___x_1699_, lean_object* v___x_1700_, lean_object* v___x_1701_, lean_object* v___x_1702_, lean_object* v_x_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
uint8_t v___x_2034__boxed_1709_; uint8_t v___x_2035__boxed_1710_; uint8_t v___x_2036__boxed_1711_; lean_object* v_res_1712_; 
v___x_2034__boxed_1709_ = lean_unbox(v___x_1700_);
v___x_2035__boxed_1710_ = lean_unbox(v___x_1701_);
v___x_2036__boxed_1711_ = lean_unbox(v___x_1702_);
v_res_1712_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(v_i_1695_, v___x_1696_, v_types_1697_, v_u_1698_, v___x_1699_, v___x_2034__boxed_1709_, v___x_2035__boxed_1710_, v___x_2036__boxed_1711_, v_x_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___x_1696_);
lean_dec(v_i_1695_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(lean_object* v_types_1716_, lean_object* v_u_1717_, lean_object* v_x_1718_, lean_object* v_i_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1725_ = lean_array_get_size(v_types_1716_);
v___x_1726_ = lean_unsigned_to_nat(1u);
v___x_1727_ = lean_nat_sub(v___x_1725_, v___x_1726_);
v___x_1728_ = lean_nat_dec_lt(v_i_1719_, v___x_1727_);
lean_dec(v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v_u_1717_);
v___x_1729_ = l_Lean_instInhabitedExpr;
v___x_1730_ = lean_array_get(v___x_1729_, v_types_1716_, v_i_1719_);
lean_dec(v_i_1719_);
lean_dec_ref(v_types_1716_);
v___x_1731_ = l_Lean_Expr_bindingBody_x21(v___x_1730_);
lean_dec(v___x_1730_);
v___x_1732_ = lean_expr_instantiate1(v___x_1731_, v_x_1718_);
lean_dec_ref(v_x_1718_);
lean_dec_ref(v___x_1731_);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; 
lean_inc(v_a_1723_);
lean_inc_ref(v_a_1722_);
lean_inc(v_a_1721_);
lean_inc_ref(v_a_1720_);
lean_inc_ref(v_x_1718_);
v___x_1734_ = lean_infer_type(v_x_1718_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = l_Lean_Meta_whnfD(v_a_1735_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1739_ = lean_unsigned_to_nat(2u);
v___x_1740_ = l_Lean_Expr_isAppOfArity(v_a_1737_, v___x_1738_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_dec(v_a_1737_);
lean_dec(v_i_1719_);
lean_dec_ref(v_x_1718_);
lean_dec(v_u_1717_);
lean_dec_ref(v_types_1716_);
v___x_1741_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2);
v___x_1742_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1741_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
return v___x_1742_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; 
lean_inc_n(v_u_1717_, 2);
v___x_1743_ = l_Lean_Level_succ___override(v_u_1717_);
v___x_1744_ = lean_mk_empty_array_with_capacity(v___x_1726_);
lean_inc_ref(v_x_1718_);
lean_inc_ref(v___x_1744_);
v___x_1745_ = lean_array_push(v___x_1744_, v_x_1718_);
v___x_1746_ = l_Lean_mkSort(v_u_1717_);
v___x_1747_ = 0;
v___x_1748_ = 1;
v___x_1749_ = l_Lean_Meta_mkLambdaFVars(v___x_1745_, v___x_1746_, v___x_1747_, v___x_1740_, v___x_1747_, v___x_1740_, v___x_1748_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
lean_dec_ref(v___x_1745_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_1752_ = l_Lean_Core_mkFreshUserName(v___x_1751_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v_nargs_1754_; lean_object* v_dummy_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
v_nargs_1754_ = l_Lean_Expr_getAppNumArgs(v_a_1737_);
v_dummy_1755_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
lean_inc(v_nargs_1754_);
v___x_1756_ = lean_mk_array(v_nargs_1754_, v_dummy_1755_);
v___x_1757_ = lean_nat_sub(v_nargs_1754_, v___x_1726_);
lean_dec(v_nargs_1754_);
lean_inc(v_a_1737_);
v___x_1758_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1737_, v___x_1756_, v___x_1757_);
v___x_1759_ = l_Lean_instInhabitedExpr;
v___x_1760_ = lean_box(v___x_1747_);
v___x_1761_ = lean_box(v___x_1740_);
v___x_1762_ = lean_box(v___x_1748_);
lean_inc(v_i_1719_);
lean_inc_ref(v_types_1716_);
lean_inc_ref(v___x_1744_);
v___f_1763_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1763_, 0, v___x_1744_);
lean_closure_set(v___f_1763_, 1, v___x_1759_);
lean_closure_set(v___f_1763_, 2, v_types_1716_);
lean_closure_set(v___f_1763_, 3, v_i_1719_);
lean_closure_set(v___f_1763_, 4, v___x_1760_);
lean_closure_set(v___f_1763_, 5, v___x_1761_);
lean_closure_set(v___f_1763_, 6, v___x_1762_);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_array_get_borrowed(v___x_1759_, v___x_1758_, v___x_1764_);
lean_inc(v___x_1765_);
v___x_1766_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1753_, v___x_1765_, v___f_1763_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = l_Lean_Core_mkFreshUserName(v___x_1751_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = lean_box(v___x_1747_);
v___x_1771_ = lean_box(v___x_1740_);
v___x_1772_ = lean_box(v___x_1748_);
v___f_1773_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed), 14, 8);
lean_closure_set(v___f_1773_, 0, v_i_1719_);
lean_closure_set(v___f_1773_, 1, v___x_1726_);
lean_closure_set(v___f_1773_, 2, v_types_1716_);
lean_closure_set(v___f_1773_, 3, v_u_1717_);
lean_closure_set(v___f_1773_, 4, v___x_1744_);
lean_closure_set(v___f_1773_, 5, v___x_1770_);
lean_closure_set(v___f_1773_, 6, v___x_1771_);
lean_closure_set(v___f_1773_, 7, v___x_1772_);
v___x_1774_ = lean_array_get(v___x_1759_, v___x_1758_, v___x_1726_);
v___x_1775_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1769_, v___x_1774_, v___f_1773_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1792_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1792_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1792_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1780_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
v___x_1781_ = l_Lean_Expr_getAppFn(v_a_1737_);
lean_dec(v_a_1737_);
v___x_1782_ = l_Lean_Expr_constLevels_x21(v___x_1781_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1743_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_mkConst(v___x_1780_, v___x_1783_);
v___x_1785_ = l_Lean_mkAppN(v___x_1784_, v___x_1758_);
lean_dec_ref(v___x_1758_);
v___x_1786_ = l_Lean_Expr_app___override(v___x_1785_, v_a_1750_);
v___x_1787_ = l_Lean_Expr_app___override(v___x_1786_, v_x_1718_);
v___x_1788_ = l_Lean_mkAppB(v___x_1787_, v_a_1767_, v_a_1776_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1788_);
v___x_1790_ = v___x_1778_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
else
{
lean_dec(v_a_1767_);
lean_dec_ref(v___x_1758_);
lean_dec(v_a_1750_);
lean_dec(v___x_1743_);
lean_dec(v_a_1737_);
lean_dec_ref(v_x_1718_);
return v___x_1775_;
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_a_1767_);
lean_dec_ref(v___x_1758_);
lean_dec(v_a_1750_);
lean_dec_ref(v___x_1744_);
lean_dec(v___x_1743_);
lean_dec(v_a_1737_);
lean_dec(v_i_1719_);
lean_dec_ref(v_x_1718_);
lean_dec(v_u_1717_);
lean_dec_ref(v_types_1716_);
v_a_1793_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1768_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1768_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_dec_ref(v___x_1758_);
lean_dec(v_a_1750_);
lean_dec_ref(v___x_1744_);
lean_dec(v___x_1743_);
lean_dec(v_a_1737_);
lean_dec(v_i_1719_);
lean_dec_ref(v_x_1718_);
lean_dec(v_u_1717_);
lean_dec_ref(v_types_1716_);
return v___x_1766_;
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v_a_1750_);
lean_dec_ref(v___x_1744_);
lean_dec(v___x_1743_);
lean_dec(v_a_1737_);
lean_dec(v_i_1719_);
lean_dec_ref(v_x_1718_);
lean_dec(v_u_1717_);
lean_dec_ref(v_types_1716_);
v_a_1801_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1752_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1752_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_dec_ref(v___x_1744_);
lean_dec(v___x_1743_);
lean_dec(v_a_1737_);
lean_dec(v_i_1719_);
lean_dec_ref(v_x_1718_);
lean_dec(v_u_1717_);
lean_dec_ref(v_types_1716_);
return v___x_1749_;
}
}
}
else
{
lean_dec(v_i_1719_);
lean_dec_ref(v_x_1718_);
lean_dec(v_u_1717_);
lean_dec_ref(v_types_1716_);
return v___x_1736_;
}
}
else
{
lean_dec(v_i_1719_);
lean_dec_ref(v_x_1718_);
lean_dec(v_u_1717_);
lean_dec_ref(v_types_1716_);
return v___x_1734_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(lean_object* v_i_1809_, lean_object* v___x_1810_, lean_object* v_types_1811_, lean_object* v_u_1812_, lean_object* v___x_1813_, uint8_t v___x_1814_, uint8_t v___x_1815_, uint8_t v___x_1816_, lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_nat_add(v_i_1809_, v___x_1810_);
lean_inc_ref(v_x_1817_);
v___x_1824_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1811_, v_u_1812_, v_x_1817_, v___x_1823_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref(v___x_1824_);
v___x_1826_ = lean_array_push(v___x_1813_, v_x_1817_);
v___x_1827_ = l_Lean_Meta_mkLambdaFVars(v___x_1826_, v_a_1825_, v___x_1814_, v___x_1815_, v___x_1814_, v___x_1815_, v___x_1816_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec_ref(v___x_1826_);
return v___x_1827_;
}
else
{
lean_dec_ref(v_x_1817_);
lean_dec_ref(v___x_1813_);
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___boxed(lean_object* v_types_1828_, lean_object* v_u_1829_, lean_object* v_x_1830_, lean_object* v_i_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1828_, v_u_1829_, v_x_1830_, v_i_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(lean_object* v_x_1838_, lean_object* v_body_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_Meta_getLevel(v_body_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed(lean_object* v_x_1846_, lean_object* v_body_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(v_x_1846_, v_body_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec_ref(v_x_1846_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(lean_object* v_types_1855_, lean_object* v_x_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v___f_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; 
v___f_1862_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0));
v___x_1863_ = l_Lean_instInhabitedExpr;
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = lean_array_get_borrowed(v___x_1863_, v_types_1855_, v___x_1864_);
v___x_1866_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_1867_ = 0;
lean_inc(v___x_1865_);
v___x_1868_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v___x_1865_, v___x_1866_, v___f_1862_, v___x_1867_, v___x_1867_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___x_1868_);
v___x_1870_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1855_, v_a_1869_, v_x_1856_, v___x_1864_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
return v___x_1870_;
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v_x_1856_);
lean_dec_ref(v_types_1855_);
v_a_1871_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1868_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1868_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___boxed(lean_object* v_types_1879_, lean_object* v_x_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_types_1879_, v_x_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(lean_object* v_a_1887_, lean_object* v___x_1888_, uint8_t v___x_1889_, lean_object* v_x_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___x_1896_; 
lean_inc_ref(v_x_1890_);
v___x_1896_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_a_1887_, v_x_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref(v___x_1896_);
v___x_1898_ = lean_mk_empty_array_with_capacity(v___x_1888_);
v___x_1899_ = lean_array_push(v___x_1898_, v_x_1890_);
v___x_1900_ = 1;
v___x_1901_ = 1;
v___x_1902_ = l_Lean_Meta_mkForallFVars(v___x_1899_, v_a_1897_, v___x_1889_, v___x_1900_, v___x_1900_, v___x_1901_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec_ref(v___x_1899_);
return v___x_1902_;
}
else
{
lean_dec_ref(v_x_1890_);
return v___x_1896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed(lean_object* v_a_1903_, lean_object* v___x_1904_, lean_object* v___x_1905_, lean_object* v_x_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
uint8_t v___x_2053__boxed_1912_; lean_object* v_res_1913_; 
v___x_2053__boxed_1912_ = lean_unbox(v___x_1905_);
v_res_1913_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(v_a_1903_, v___x_1904_, v___x_2053__boxed_1912_, v_x_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___x_1904_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(size_t v_sz_1914_, size_t v_i_1915_, lean_object* v_bs_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_usize_dec_lt(v_i_1915_, v_sz_1914_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_bs_1916_);
return v___x_1923_;
}
else
{
lean_object* v_v_1924_; lean_object* v___x_1925_; 
v_v_1924_ = lean_array_uget_borrowed(v_bs_1916_, v_i_1915_);
lean_inc(v_v_1924_);
v___x_1925_ = l_Lean_Meta_whnfForall(v_v_1924_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; lean_object* v_bs_x27_1928_; size_t v___x_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1925_);
v___x_1927_ = lean_unsigned_to_nat(0u);
v_bs_x27_1928_ = lean_array_uset(v_bs_1916_, v_i_1915_, v___x_1927_);
v___x_1929_ = ((size_t)1ULL);
v___x_1930_ = lean_usize_add(v_i_1915_, v___x_1929_);
v___x_1931_ = lean_array_uset(v_bs_x27_1928_, v_i_1915_, v_a_1926_);
v_i_1915_ = v___x_1930_;
v_bs_1916_ = v___x_1931_;
goto _start;
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec_ref(v_bs_1916_);
v_a_1933_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1925_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1925_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0___boxed(lean_object* v_sz_1941_, lean_object* v_i_1942_, lean_object* v_bs_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
size_t v_sz_boxed_1949_; size_t v_i_boxed_1950_; lean_object* v_res_1951_; 
v_sz_boxed_1949_ = lean_unbox_usize(v_sz_1941_);
lean_dec(v_sz_1941_);
v_i_boxed_1950_ = lean_unbox_usize(v_i_1942_);
lean_dec(v_i_1942_);
v_res_1951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_boxed_1949_, v_i_boxed_1950_, v_bs_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1951_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0));
v___x_1954_ = l_Lean_stringToMessageData(v___x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(lean_object* v_as_1955_, size_t v_i_1956_, size_t v_stop_1957_, lean_object* v_b_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_a_1965_; uint8_t v___x_1969_; 
v___x_1969_ = lean_usize_dec_eq(v_i_1956_, v_stop_1957_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1970_ = lean_array_uget_borrowed(v_as_1955_, v_i_1956_);
v___x_1971_ = l_Lean_Expr_isForall(v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1972_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1);
lean_inc(v___x_1970_);
v___x_1973_ = l_Lean_MessageData_ofExpr(v___x_1970_);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1974_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref(v___x_1975_);
v_a_1965_ = v_a_1976_;
goto v___jp_1964_;
}
else
{
return v___x_1975_;
}
}
else
{
lean_object* v___x_1977_; 
v___x_1977_ = lean_box(0);
v_a_1965_ = v___x_1977_;
goto v___jp_1964_;
}
}
else
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v_b_1958_);
return v___x_1978_;
}
v___jp_1964_:
{
size_t v___x_1966_; size_t v___x_1967_; 
v___x_1966_ = ((size_t)1ULL);
v___x_1967_ = lean_usize_add(v_i_1956_, v___x_1966_);
v_i_1956_ = v___x_1967_;
v_b_1958_ = v_a_1965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___boxed(lean_object* v_as_1979_, lean_object* v_i_1980_, lean_object* v_stop_1981_, lean_object* v_b_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
size_t v_i_boxed_1988_; size_t v_stop_boxed_1989_; lean_object* v_res_1990_; 
v_i_boxed_1988_ = lean_unbox_usize(v_i_1980_);
lean_dec(v_i_1980_);
v_stop_boxed_1989_ = lean_unbox_usize(v_stop_1981_);
lean_dec(v_stop_1981_);
v_res_1990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_as_1979_, v_i_boxed_1988_, v_stop_boxed_1989_, v_b_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec_ref(v_as_1979_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(size_t v_sz_1991_, size_t v_i_1992_, lean_object* v_bs_1993_){
_start:
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_usize_dec_lt(v_i_1992_, v_sz_1991_);
if (v___x_1994_ == 0)
{
return v_bs_1993_;
}
else
{
lean_object* v_v_1995_; lean_object* v___x_1996_; lean_object* v_bs_x27_1997_; lean_object* v___x_1998_; size_t v___x_1999_; size_t v___x_2000_; lean_object* v___x_2001_; 
v_v_1995_ = lean_array_uget(v_bs_1993_, v_i_1992_);
v___x_1996_ = lean_unsigned_to_nat(0u);
v_bs_x27_1997_ = lean_array_uset(v_bs_1993_, v_i_1992_, v___x_1996_);
v___x_1998_ = l_Lean_Expr_bindingDomain_x21(v_v_1995_);
lean_dec(v_v_1995_);
v___x_1999_ = ((size_t)1ULL);
v___x_2000_ = lean_usize_add(v_i_1992_, v___x_1999_);
v___x_2001_ = lean_array_uset(v_bs_x27_1997_, v_i_1992_, v___x_1998_);
v_i_1992_ = v___x_2000_;
v_bs_1993_ = v___x_2001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1___boxed(lean_object* v_sz_2003_, lean_object* v_i_2004_, lean_object* v_bs_2005_){
_start:
{
size_t v_sz_boxed_2006_; size_t v_i_boxed_2007_; lean_object* v_res_2008_; 
v_sz_boxed_2006_ = lean_unbox_usize(v_sz_2003_);
lean_dec(v_sz_2003_);
v_i_boxed_2007_ = lean_unbox_usize(v_i_2004_);
lean_dec(v_i_2004_);
v_res_2008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_boxed_2006_, v_i_boxed_2007_, v_bs_2005_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType(lean_object* v_types_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2015_ = lean_array_get_size(v_types_2009_);
v___x_2016_ = lean_unsigned_to_nat(1u);
v___x_2017_ = lean_nat_dec_eq(v___x_2015_, v___x_2016_);
if (v___x_2017_ == 0)
{
size_t v_sz_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v_sz_2018_ = lean_array_size(v_types_2009_);
v___x_2019_ = ((size_t)0ULL);
v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2018_, v___x_2019_, v_types_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; lean_object* v___f_2023_; lean_object* v___y_2042_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc_n(v_a_2021_, 2);
lean_dec_ref(v___x_2020_);
v___x_2022_ = lean_box(v___x_2017_);
v___f_2023_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2023_, 0, v_a_2021_);
lean_closure_set(v___f_2023_, 1, v___x_2016_);
lean_closure_set(v___f_2023_, 2, v___x_2022_);
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = lean_array_get_size(v_a_2021_);
v___x_2053_ = lean_nat_dec_lt(v___x_2051_, v___x_2052_);
if (v___x_2053_ == 0)
{
goto v___jp_2024_;
}
else
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_nat_dec_le(v___x_2052_, v___x_2052_);
if (v___x_2055_ == 0)
{
if (v___x_2053_ == 0)
{
goto v___jp_2024_;
}
else
{
size_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_usize_of_nat(v___x_2052_);
v___x_2057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_2021_, v___x_2019_, v___x_2056_, v___x_2054_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
v___y_2042_ = v___x_2057_;
goto v___jp_2041_;
}
}
else
{
size_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_usize_of_nat(v___x_2052_);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_2021_, v___x_2019_, v___x_2058_, v___x_2054_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
v___y_2042_ = v___x_2059_;
goto v___jp_2041_;
}
}
v___jp_2024_:
{
size_t v_sz_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_sz_2025_ = lean_array_size(v_a_2021_);
v___x_2026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_2025_, v___x_2019_, v_a_2021_);
v___x_2027_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2026_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v___x_2029_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2030_ = l_Lean_Core_mkFreshUserName(v___x_2029_, v_a_2012_, v_a_2013_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref(v___x_2030_);
v___x_2032_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2031_, v_a_2028_, v___f_2023_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
return v___x_2032_;
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_a_2028_);
lean_dec_ref(v___f_2023_);
v_a_2033_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2030_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2030_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
lean_dec_ref(v___f_2023_);
return v___x_2027_;
}
}
v___jp_2041_:
{
if (lean_obj_tag(v___y_2042_) == 0)
{
lean_dec_ref(v___y_2042_);
goto v___jp_2024_;
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v___f_2023_);
lean_dec(v_a_2021_);
v_a_2043_ = lean_ctor_get(v___y_2042_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___y_2042_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___y_2042_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___y_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
v_a_2060_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2020_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2020_);
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
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = l_Lean_instInhabitedExpr;
v___x_2069_ = lean_unsigned_to_nat(0u);
v___x_2070_ = lean_array_get(v___x_2068_, v_types_2009_, v___x_2069_);
lean_dec_ref(v_types_2009_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___boxed(lean_object* v_types_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_types_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
return v_res_2078_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0));
v___x_2081_ = l_Lean_stringToMessageData(v___x_2080_);
return v___x_2081_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2));
v___x_2084_ = l_Lean_stringToMessageData(v___x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(lean_object* v___x_2085_, lean_object* v_as_2086_, size_t v_i_2087_, size_t v_stop_2088_, lean_object* v_b_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_a_2096_; uint8_t v___x_2100_; 
v___x_2100_ = lean_usize_dec_eq(v_i_2087_, v_stop_2088_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_array_uget_borrowed(v_as_2086_, v_i_2087_);
lean_inc_ref(v___x_2085_);
lean_inc(v___x_2101_);
v___x_2102_ = l_Lean_Meta_isExprDefEq(v___x_2101_, v___x_2085_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; uint8_t v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref(v___x_2102_);
v___x_2104_ = lean_unbox(v_a_2103_);
lean_dec(v_a_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2105_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1);
lean_inc(v___x_2101_);
v___x_2106_ = l_Lean_MessageData_ofExpr(v___x_2101_);
v___x_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3);
v___x_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
lean_inc_ref(v___x_2085_);
v___x_2110_ = l_Lean_MessageData_ofExpr(v___x_2085_);
v___x_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2111_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref(v___x_2112_);
v_a_2096_ = v_a_2113_;
goto v___jp_2095_;
}
else
{
lean_dec_ref(v___x_2085_);
return v___x_2112_;
}
}
else
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_box(0);
v_a_2096_ = v___x_2114_;
goto v___jp_2095_;
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v___x_2085_);
v_a_2115_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2102_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2102_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_object* v___x_2123_; 
lean_dec_ref(v___x_2085_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_b_2089_);
return v___x_2123_;
}
v___jp_2095_:
{
size_t v___x_2097_; size_t v___x_2098_; 
v___x_2097_ = ((size_t)1ULL);
v___x_2098_ = lean_usize_add(v_i_2087_, v___x_2097_);
v_i_2087_ = v___x_2098_;
v_b_2089_ = v_a_2096_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___boxed(lean_object* v___x_2124_, lean_object* v_as_2125_, lean_object* v_i_2126_, lean_object* v_stop_2127_, lean_object* v_b_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
size_t v_i_boxed_2134_; size_t v_stop_boxed_2135_; lean_object* v_res_2136_; 
v_i_boxed_2134_ = lean_unbox_usize(v_i_2126_);
lean_dec(v_i_2126_);
v_stop_boxed_2135_ = lean_unbox_usize(v_stop_2127_);
lean_dec(v_stop_2127_);
v_res_2136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2124_, v_as_2125_, v_i_boxed_2134_, v_stop_boxed_2135_, v_b_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec_ref(v_as_2125_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(size_t v_sz_2137_, size_t v_i_2138_, lean_object* v_bs_2139_){
_start:
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_usize_dec_lt(v_i_2138_, v_sz_2137_);
if (v___x_2140_ == 0)
{
return v_bs_2139_;
}
else
{
lean_object* v_v_2141_; lean_object* v___x_2142_; lean_object* v_bs_x27_2143_; lean_object* v___x_2144_; size_t v___x_2145_; size_t v___x_2146_; lean_object* v___x_2147_; 
v_v_2141_ = lean_array_uget(v_bs_2139_, v_i_2138_);
v___x_2142_ = lean_unsigned_to_nat(0u);
v_bs_x27_2143_ = lean_array_uset(v_bs_2139_, v_i_2138_, v___x_2142_);
v___x_2144_ = l_Lean_Expr_bindingBody_x21(v_v_2141_);
lean_dec(v_v_2141_);
v___x_2145_ = ((size_t)1ULL);
v___x_2146_ = lean_usize_add(v_i_2138_, v___x_2145_);
v___x_2147_ = lean_array_uset(v_bs_x27_2143_, v_i_2138_, v___x_2144_);
v_i_2138_ = v___x_2146_;
v_bs_2139_ = v___x_2147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0___boxed(lean_object* v_sz_2149_, lean_object* v_i_2150_, lean_object* v_bs_2151_){
_start:
{
size_t v_sz_boxed_2152_; size_t v_i_boxed_2153_; lean_object* v_res_2154_; 
v_sz_boxed_2152_ = lean_unbox_usize(v_sz_2149_);
lean_dec(v_sz_2149_);
v_i_boxed_2153_ = lean_unbox_usize(v_i_2150_);
lean_dec(v_i_2150_);
v_res_2154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_boxed_2152_, v_i_boxed_2153_, v_bs_2151_);
return v_res_2154_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0));
v___x_2157_ = l_Lean_stringToMessageData(v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(lean_object* v_as_2158_, size_t v_i_2159_, size_t v_stop_2160_, lean_object* v_b_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_a_2168_; uint8_t v___x_2172_; 
v___x_2172_ = lean_usize_dec_eq(v_i_2159_, v_stop_2160_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = lean_array_uget_borrowed(v_as_2158_, v_i_2159_);
v___x_2174_ = l_Lean_Expr_isArrow(v___x_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2175_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1);
lean_inc(v___x_2173_);
v___x_2176_ = l_Lean_MessageData_ofExpr(v___x_2173_);
v___x_2177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2177_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref(v___x_2178_);
v_a_2168_ = v_a_2179_;
goto v___jp_2167_;
}
else
{
return v___x_2178_;
}
}
else
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_box(0);
v_a_2168_ = v___x_2180_;
goto v___jp_2167_;
}
}
else
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_b_2161_);
return v___x_2181_;
}
v___jp_2167_:
{
size_t v___x_2169_; size_t v___x_2170_; 
v___x_2169_ = ((size_t)1ULL);
v___x_2170_ = lean_usize_add(v_i_2159_, v___x_2169_);
v_i_2159_ = v___x_2170_;
v_b_2161_ = v_a_2168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___boxed(lean_object* v_as_2182_, lean_object* v_i_2183_, lean_object* v_stop_2184_, lean_object* v_b_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
size_t v_i_boxed_2191_; size_t v_stop_boxed_2192_; lean_object* v_res_2193_; 
v_i_boxed_2191_ = lean_unbox_usize(v_i_2183_);
lean_dec(v_i_2183_);
v_stop_boxed_2192_ = lean_unbox_usize(v_stop_2184_);
lean_dec(v_stop_2184_);
v_res_2193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_as_2182_, v_i_boxed_2191_, v_stop_boxed_2192_, v_b_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec_ref(v_as_2182_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(lean_object* v_types_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
size_t v_sz_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
v_sz_2200_ = lean_array_size(v_types_2194_);
v___x_2201_ = ((size_t)0ULL);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2200_, v___x_2201_, v_types_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___y_2207_; size_t v___y_2208_; lean_object* v___y_2215_; size_t v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2243_; lean_object* v___x_2252_; uint8_t v___x_2253_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = l_Lean_instInhabitedExpr;
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2252_ = lean_array_get_size(v_a_2203_);
v___x_2253_ = lean_nat_dec_lt(v___x_2205_, v___x_2252_);
if (v___x_2253_ == 0)
{
goto v___jp_2226_;
}
else
{
lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2254_ = lean_box(0);
v___x_2255_ = lean_nat_dec_le(v___x_2252_, v___x_2252_);
if (v___x_2255_ == 0)
{
if (v___x_2253_ == 0)
{
goto v___jp_2226_;
}
else
{
size_t v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_usize_of_nat(v___x_2252_);
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2203_, v___x_2201_, v___x_2256_, v___x_2254_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
v___y_2243_ = v___x_2257_;
goto v___jp_2242_;
}
}
else
{
size_t v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_usize_of_nat(v___x_2252_);
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2203_, v___x_2201_, v___x_2258_, v___x_2254_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
v___y_2243_ = v___x_2259_;
goto v___jp_2242_;
}
}
v___jp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v___y_2208_, v___x_2201_, v_a_2203_);
v___x_2210_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2209_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref(v___x_2210_);
v___x_2212_ = lean_array_get(v___x_2204_, v___y_2207_, v___x_2205_);
lean_dec_ref(v___y_2207_);
v___x_2213_ = l_Lean_mkArrow(v_a_2211_, v___x_2212_, v_a_2197_, v_a_2198_);
return v___x_2213_;
}
else
{
lean_dec_ref(v___y_2207_);
return v___x_2210_;
}
}
v___jp_2214_:
{
if (lean_obj_tag(v___y_2217_) == 0)
{
lean_dec_ref(v___y_2217_);
v___y_2207_ = v___y_2215_;
v___y_2208_ = v___y_2216_;
goto v___jp_2206_;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v___y_2215_);
lean_dec(v_a_2203_);
v_a_2218_ = lean_ctor_get(v___y_2217_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___y_2217_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___y_2217_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___y_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
v___jp_2226_:
{
size_t v_sz_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v_sz_2227_ = lean_array_size(v_a_2203_);
lean_inc(v_a_2203_);
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_2227_, v___x_2201_, v_a_2203_);
v___x_2229_ = lean_array_get_size(v___x_2228_);
v___x_2230_ = lean_unsigned_to_nat(1u);
v___x_2231_ = lean_nat_sub(v___x_2229_, v___x_2230_);
v___x_2232_ = lean_array_get(v___x_2204_, v___x_2228_, v___x_2231_);
lean_dec(v___x_2231_);
lean_inc_ref(v___x_2228_);
v___x_2233_ = lean_array_pop(v___x_2228_);
v___x_2234_ = lean_array_get_size(v___x_2233_);
v___x_2235_ = lean_nat_dec_lt(v___x_2205_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_dec_ref(v___x_2233_);
lean_dec(v___x_2232_);
v___y_2207_ = v___x_2228_;
v___y_2208_ = v_sz_2227_;
goto v___jp_2206_;
}
else
{
lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2236_ = lean_box(0);
v___x_2237_ = lean_nat_dec_le(v___x_2234_, v___x_2234_);
if (v___x_2237_ == 0)
{
if (v___x_2235_ == 0)
{
lean_dec_ref(v___x_2233_);
lean_dec(v___x_2232_);
v___y_2207_ = v___x_2228_;
v___y_2208_ = v_sz_2227_;
goto v___jp_2206_;
}
else
{
size_t v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_usize_of_nat(v___x_2234_);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2232_, v___x_2233_, v___x_2201_, v___x_2238_, v___x_2236_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec_ref(v___x_2233_);
v___y_2215_ = v___x_2228_;
v___y_2216_ = v_sz_2227_;
v___y_2217_ = v___x_2239_;
goto v___jp_2214_;
}
}
else
{
size_t v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_usize_of_nat(v___x_2234_);
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2232_, v___x_2233_, v___x_2201_, v___x_2240_, v___x_2236_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec_ref(v___x_2233_);
v___y_2215_ = v___x_2228_;
v___y_2216_ = v_sz_2227_;
v___y_2217_ = v___x_2241_;
goto v___jp_2214_;
}
}
}
v___jp_2242_:
{
if (lean_obj_tag(v___y_2243_) == 0)
{
lean_dec_ref(v___y_2243_);
goto v___jp_2226_;
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_a_2203_);
v_a_2244_ = lean_ctor_get(v___y_2243_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___y_2243_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___y_2243_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___y_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
v_a_2260_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2202_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2202_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND___boxed(lean_object* v_types_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_types_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
return v_res_2274_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0));
v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
return v___x_2277_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2));
v___x_2280_ = l_Lean_stringToMessageData(v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed(lean_object* v___x_2281_, lean_object* v___x_2282_, lean_object* v_arg_2283_, lean_object* v_arg_2284_, lean_object* v___x_2285_, lean_object* v_a_2286_, lean_object* v_tail_2287_, lean_object* v___x_2288_, lean_object* v___x_2289_, lean_object* v___x_2290_, lean_object* v_y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
uint8_t v___x_3071__boxed_2297_; uint8_t v___x_3072__boxed_2298_; uint8_t v___x_3073__boxed_2299_; lean_object* v_res_2300_; 
v___x_3071__boxed_2297_ = lean_unbox(v___x_2288_);
v___x_3072__boxed_2298_ = lean_unbox(v___x_2289_);
v___x_3073__boxed_2299_ = lean_unbox(v___x_2290_);
v_res_2300_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(v___x_2281_, v___x_2282_, v_arg_2283_, v_arg_2284_, v___x_2285_, v_a_2286_, v_tail_2287_, v___x_3071__boxed_2297_, v___x_3072__boxed_2298_, v___x_3073__boxed_2299_, v_y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(lean_object* v_x_2301_, lean_object* v_codomain_2302_, lean_object* v_alts_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
if (lean_obj_tag(v_alts_2303_) == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_dec_ref(v_codomain_2302_);
lean_dec_ref(v_x_2301_);
v___x_2309_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1);
v___x_2310_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2309_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
return v___x_2310_;
}
else
{
lean_object* v_tail_2311_; 
v_tail_2311_ = lean_ctor_get(v_alts_2303_, 1);
if (lean_obj_tag(v_tail_2311_) == 0)
{
lean_object* v_head_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_dec_ref(v_codomain_2302_);
v_head_2312_ = lean_ctor_get(v_alts_2303_, 0);
lean_inc(v_head_2312_);
lean_dec_ref(v_alts_2303_);
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = lean_mk_empty_array_with_capacity(v___x_2313_);
v___x_2315_ = lean_array_push(v___x_2314_, v_x_2301_);
v___x_2316_ = l_Lean_Expr_beta(v_head_2312_, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
else
{
lean_object* v_head_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2403_; 
lean_inc(v_tail_2311_);
v_head_2318_ = lean_ctor_get(v_alts_2303_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_alts_2303_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v_alts_2303_, 1);
lean_dec(v_unused_2404_);
v___x_2320_ = v_alts_2303_;
v_isShared_2321_ = v_isSharedCheck_2403_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_head_2318_);
lean_dec(v_alts_2303_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2403_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; 
lean_inc(v_a_2307_);
lean_inc_ref(v_a_2306_);
lean_inc(v_a_2305_);
lean_inc_ref(v_a_2304_);
lean_inc_ref(v_x_2301_);
v___x_2322_ = lean_infer_type(v_x_2301_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2324_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc_n(v_a_2323_, 2);
lean_dec_ref(v___x_2322_);
v___x_2324_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2323_, v_a_2305_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref(v___x_2324_);
v___x_2335_ = l_Lean_Expr_cleanupAnnotations(v_a_2325_);
v___x_2336_ = l_Lean_Expr_isApp(v___x_2335_);
if (v___x_2336_ == 0)
{
lean_dec_ref(v___x_2335_);
lean_del_object(v___x_2320_);
lean_dec(v_head_2318_);
lean_dec(v_tail_2311_);
lean_dec_ref(v_codomain_2302_);
lean_dec_ref(v_x_2301_);
v___y_2327_ = v_a_2304_;
v___y_2328_ = v_a_2305_;
v___y_2329_ = v_a_2306_;
v___y_2330_ = v_a_2307_;
goto v___jp_2326_;
}
else
{
lean_object* v_arg_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_arg_2337_ = lean_ctor_get(v___x_2335_, 1);
lean_inc_ref(v_arg_2337_);
v___x_2338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2335_);
v___x_2339_ = l_Lean_Expr_isApp(v___x_2338_);
if (v___x_2339_ == 0)
{
lean_dec_ref(v___x_2338_);
lean_dec_ref(v_arg_2337_);
lean_del_object(v___x_2320_);
lean_dec(v_head_2318_);
lean_dec(v_tail_2311_);
lean_dec_ref(v_codomain_2302_);
lean_dec_ref(v_x_2301_);
v___y_2327_ = v_a_2304_;
v___y_2328_ = v_a_2305_;
v___y_2329_ = v_a_2306_;
v___y_2330_ = v_a_2307_;
goto v___jp_2326_;
}
else
{
lean_object* v_arg_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v_arg_2340_ = lean_ctor_get(v___x_2338_, 1);
lean_inc_ref(v_arg_2340_);
v___x_2341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2338_);
v___x_2342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0));
v___x_2343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_2344_ = l_Lean_Expr_isConstOf(v___x_2341_, v___x_2343_);
lean_dec_ref(v___x_2341_);
if (v___x_2344_ == 0)
{
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_del_object(v___x_2320_);
lean_dec(v_head_2318_);
lean_dec(v_tail_2311_);
lean_dec_ref(v_codomain_2302_);
lean_dec_ref(v_x_2301_);
v___y_2327_ = v_a_2304_;
v___y_2328_ = v_a_2305_;
v___y_2329_ = v_a_2306_;
v___y_2330_ = v_a_2307_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2345_; 
lean_inc_ref(v_codomain_2302_);
v___x_2345_ = l_Lean_Meta_getLevel(v_codomain_2302_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; uint8_t v___x_2351_; lean_object* v___x_2352_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2345_);
v___x_2347_ = lean_unsigned_to_nat(1u);
v___x_2348_ = lean_mk_empty_array_with_capacity(v___x_2347_);
lean_inc_ref(v_x_2301_);
lean_inc_ref(v___x_2348_);
v___x_2349_ = lean_array_push(v___x_2348_, v_x_2301_);
v___x_2350_ = 0;
v___x_2351_ = 1;
v___x_2352_ = l_Lean_Meta_mkLambdaFVars(v___x_2349_, v_codomain_2302_, v___x_2350_, v___x_2344_, v___x_2350_, v___x_2344_, v___x_2351_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
lean_dec_ref(v___x_2349_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2394_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2394_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2394_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v_alt_u2082_2360_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___f_2373_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; 
v___x_2357_ = l_Lean_Expr_getAppFn(v_a_2323_);
lean_dec(v_a_2323_);
v___x_2358_ = l_Lean_Expr_constLevels_x21(v___x_2357_);
lean_dec_ref(v___x_2357_);
v___x_2370_ = lean_box(v___x_2350_);
v___x_2371_ = lean_box(v___x_2344_);
v___x_2372_ = lean_box(v___x_2351_);
lean_inc(v_tail_2311_);
lean_inc(v_a_2353_);
lean_inc_ref(v_arg_2337_);
lean_inc_ref(v_arg_2340_);
lean_inc(v___x_2358_);
v___f_2373_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2373_, 0, v___x_2342_);
lean_closure_set(v___f_2373_, 1, v___x_2358_);
lean_closure_set(v___f_2373_, 2, v_arg_2340_);
lean_closure_set(v___f_2373_, 3, v_arg_2337_);
lean_closure_set(v___f_2373_, 4, v___x_2348_);
lean_closure_set(v___f_2373_, 5, v_a_2353_);
lean_closure_set(v___f_2373_, 6, v_tail_2311_);
lean_closure_set(v___f_2373_, 7, v___x_2370_);
lean_closure_set(v___f_2373_, 8, v___x_2371_);
lean_closure_set(v___f_2373_, 9, v___x_2372_);
if (lean_obj_tag(v_tail_2311_) == 1)
{
lean_object* v_tail_2392_; 
v_tail_2392_ = lean_ctor_get(v_tail_2311_, 1);
if (lean_obj_tag(v_tail_2392_) == 0)
{
lean_object* v_head_2393_; 
lean_dec_ref(v___f_2373_);
v_head_2393_ = lean_ctor_get(v_tail_2311_, 0);
lean_inc(v_head_2393_);
lean_dec_ref(v_tail_2311_);
v_alt_u2082_2360_ = v_head_2393_;
goto v___jp_2359_;
}
else
{
lean_dec_ref(v_tail_2311_);
v___y_2375_ = v_a_2304_;
v___y_2376_ = v_a_2305_;
v___y_2377_ = v_a_2306_;
v___y_2378_ = v_a_2307_;
goto v___jp_2374_;
}
}
else
{
lean_dec(v_tail_2311_);
v___y_2375_ = v_a_2304_;
v___y_2376_ = v_a_2305_;
v___y_2377_ = v_a_2306_;
v___y_2378_ = v_a_2307_;
goto v___jp_2374_;
}
v___jp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2361_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___x_2358_);
lean_ctor_set(v___x_2320_, 0, v_a_2346_);
v___x_2363_ = v___x_2320_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2346_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_2358_);
v___x_2363_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2364_ = l_Lean_Expr_const___override(v___x_2361_, v___x_2363_);
v___x_2365_ = l_Lean_mkApp6(v___x_2364_, v_arg_2340_, v_arg_2337_, v_a_2353_, v_x_2301_, v_head_2318_, v_alt_u2082_2360_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2365_);
v___x_2367_ = v___x_2355_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
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
v___jp_2374_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_2380_ = l_Lean_Core_mkFreshUserName(v___x_2379_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2382_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref(v___x_2380_);
lean_inc_ref(v_arg_2337_);
v___x_2382_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2381_, v_arg_2337_, v___f_2373_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref(v___x_2382_);
v_alt_u2082_2360_ = v_a_2383_;
goto v___jp_2359_;
}
else
{
lean_dec(v___x_2358_);
lean_del_object(v___x_2355_);
lean_dec(v_a_2353_);
lean_dec(v_a_2346_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_del_object(v___x_2320_);
lean_dec(v_head_2318_);
lean_dec_ref(v_x_2301_);
return v___x_2382_;
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec_ref(v___f_2373_);
lean_dec(v___x_2358_);
lean_del_object(v___x_2355_);
lean_dec(v_a_2353_);
lean_dec(v_a_2346_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_del_object(v___x_2320_);
lean_dec(v_head_2318_);
lean_dec_ref(v_x_2301_);
v_a_2384_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2380_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2380_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2348_);
lean_dec(v_a_2346_);
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec(v_a_2323_);
lean_del_object(v___x_2320_);
lean_dec(v_head_2318_);
lean_dec(v_tail_2311_);
lean_dec_ref(v_x_2301_);
return v___x_2352_;
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec_ref(v_arg_2340_);
lean_dec_ref(v_arg_2337_);
lean_dec(v_a_2323_);
lean_del_object(v___x_2320_);
lean_dec(v_head_2318_);
lean_dec(v_tail_2311_);
lean_dec_ref(v_codomain_2302_);
lean_dec_ref(v_x_2301_);
v_a_2395_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2345_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2345_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
}
v___jp_2326_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2331_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3);
v___x_2332_ = l_Lean_MessageData_ofExpr(v_a_2323_);
v___x_2333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2333_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
return v___x_2334_;
}
}
else
{
lean_dec(v_a_2323_);
lean_del_object(v___x_2320_);
lean_dec(v_head_2318_);
lean_dec(v_tail_2311_);
lean_dec_ref(v_codomain_2302_);
lean_dec_ref(v_x_2301_);
return v___x_2324_;
}
}
else
{
lean_del_object(v___x_2320_);
lean_dec(v_head_2318_);
lean_dec(v_tail_2311_);
lean_dec_ref(v_codomain_2302_);
lean_dec_ref(v_x_2301_);
return v___x_2322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(lean_object* v___x_2405_, lean_object* v___x_2406_, lean_object* v_arg_2407_, lean_object* v_arg_2408_, lean_object* v___x_2409_, lean_object* v_a_2410_, lean_object* v_tail_2411_, uint8_t v___x_2412_, uint8_t v___x_2413_, uint8_t v___x_2414_, lean_object* v_y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2421_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3));
v___x_2422_ = l_Lean_Name_mkStr2(v___x_2405_, v___x_2421_);
v___x_2423_ = l_Lean_Expr_const___override(v___x_2422_, v___x_2406_);
lean_inc_ref_n(v_y_2415_, 2);
v___x_2424_ = l_Lean_mkApp3(v___x_2423_, v_arg_2407_, v_arg_2408_, v_y_2415_);
lean_inc_ref(v___x_2409_);
v___x_2425_ = lean_array_push(v___x_2409_, v___x_2424_);
v___x_2426_ = l_Lean_Expr_beta(v_a_2410_, v___x_2425_);
v___x_2427_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_y_2415_, v___x_2426_, v_tail_2411_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref(v___x_2427_);
v___x_2429_ = lean_array_push(v___x_2409_, v_y_2415_);
v___x_2430_ = l_Lean_Meta_mkLambdaFVars(v___x_2429_, v_a_2428_, v___x_2412_, v___x_2413_, v___x_2412_, v___x_2413_, v___x_2414_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec_ref(v___x_2429_);
return v___x_2430_;
}
else
{
lean_dec_ref(v_y_2415_);
lean_dec_ref(v___x_2409_);
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___boxed(lean_object* v_x_2431_, lean_object* v_codomain_2432_, lean_object* v_alts_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_x_2431_, v_codomain_2432_, v_alts_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
return v_res_2439_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2441_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2442_ = lean_unsigned_to_nat(21u);
v___x_2443_ = lean_unsigned_to_nat(414u);
v___x_2444_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0));
v___x_2445_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2446_ = l_mkPanicMessageWithDecl(v___x_2445_, v___x_2444_, v___x_2443_, v___x_2442_, v___x_2441_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(lean_object* v___x_2447_, lean_object* v_es_2448_, lean_object* v_xs_2449_, lean_object* v_codomain_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = lean_array_get_size(v_xs_2449_);
v___x_2457_ = lean_nat_dec_eq(v___x_2456_, v___x_2447_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
lean_dec_ref(v_codomain_2450_);
lean_dec_ref(v_es_2448_);
v___x_2458_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1);
v___x_2459_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2458_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
return v___x_2459_;
}
else
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2460_ = lean_unsigned_to_nat(0u);
v___x_2461_ = lean_array_fget_borrowed(v_xs_2449_, v___x_2460_);
v___x_2462_ = lean_array_to_list(v_es_2448_);
lean_inc(v___x_2461_);
v___x_2463_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2461_, v_codomain_2450_, v___x_2462_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref(v___x_2463_);
v___x_2465_ = lean_mk_empty_array_with_capacity(v___x_2447_);
lean_inc(v___x_2461_);
v___x_2466_ = lean_array_push(v___x_2465_, v___x_2461_);
v___x_2467_ = 0;
v___x_2468_ = 1;
v___x_2469_ = l_Lean_Meta_mkLambdaFVars(v___x_2466_, v_a_2464_, v___x_2467_, v___x_2457_, v___x_2467_, v___x_2457_, v___x_2468_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec_ref(v___x_2466_);
return v___x_2469_;
}
else
{
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed(lean_object* v___x_2470_, lean_object* v_es_2471_, lean_object* v_xs_2472_, lean_object* v_codomain_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(v___x_2470_, v_es_2471_, v_xs_2472_, v_codomain_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v_xs_2472_);
lean_dec(v___x_2470_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(lean_object* v_resultType_2480_, lean_object* v_es_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v___x_2487_; lean_object* v___f_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; lean_object* v___x_2491_; 
v___x_2487_ = lean_unsigned_to_nat(1u);
v___f_2488_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2488_, 0, v___x_2487_);
lean_closure_set(v___f_2488_, 1, v_es_2481_);
v___x_2489_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2490_ = 0;
v___x_2491_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_resultType_2480_, v___x_2489_, v___f_2488_, v___x_2490_, v___x_2490_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___boxed(lean_object* v_resultType_2492_, lean_object* v_es_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_2492_, v_es_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(size_t v_sz_2500_, size_t v_i_2501_, lean_object* v_bs_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
uint8_t v___x_2508_; 
v___x_2508_ = lean_usize_dec_lt(v_i_2501_, v_sz_2500_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_bs_2502_);
return v___x_2509_;
}
else
{
lean_object* v_v_2510_; lean_object* v___x_2511_; 
v_v_2510_ = lean_array_uget_borrowed(v_bs_2502_, v_i_2501_);
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
lean_inc(v_v_2510_);
v___x_2511_ = lean_infer_type(v_v_2510_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2513_; lean_object* v_bs_x27_2514_; size_t v___x_2515_; size_t v___x_2516_; lean_object* v___x_2517_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref(v___x_2511_);
v___x_2513_ = lean_unsigned_to_nat(0u);
v_bs_x27_2514_ = lean_array_uset(v_bs_2502_, v_i_2501_, v___x_2513_);
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_add(v_i_2501_, v___x_2515_);
v___x_2517_ = lean_array_uset(v_bs_x27_2514_, v_i_2501_, v_a_2512_);
v_i_2501_ = v___x_2516_;
v_bs_2502_ = v___x_2517_;
goto _start;
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v_bs_2502_);
v_a_2519_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2511_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2511_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0___boxed(lean_object* v_sz_2527_, lean_object* v_i_2528_, lean_object* v_bs_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
size_t v_sz_boxed_2535_; size_t v_i_boxed_2536_; lean_object* v_res_2537_; 
v_sz_boxed_2535_ = lean_unbox_usize(v_sz_2527_);
lean_dec(v_sz_2527_);
v_i_boxed_2536_ = lean_unbox_usize(v_i_2528_);
lean_dec(v_i_2528_);
v_res_2537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_boxed_2535_, v_i_boxed_2536_, v_bs_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry(lean_object* v_es_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
size_t v_sz_2544_; size_t v___x_2545_; lean_object* v___x_2546_; 
v_sz_2544_ = lean_array_size(v_es_2538_);
v___x_2545_ = ((size_t)0ULL);
lean_inc_ref(v_es_2538_);
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2544_, v___x_2545_, v_es_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2547_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2548_);
v___x_2550_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_a_2549_, v_es_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
return v___x_2550_;
}
else
{
lean_dec_ref(v_es_2538_);
return v___x_2548_;
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec_ref(v_es_2538_);
v_a_2551_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2546_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2546_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry___boxed(lean_object* v_es_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_es_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
return v_res_2565_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2567_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2568_ = lean_unsigned_to_nat(21u);
v___x_2569_ = lean_unsigned_to_nat(434u);
v___x_2570_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0));
v___x_2571_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2572_ = l_mkPanicMessageWithDecl(v___x_2571_, v___x_2570_, v___x_2569_, v___x_2568_, v___x_2567_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(lean_object* v___x_2573_, lean_object* v_es_2574_, lean_object* v_xs_2575_, lean_object* v_codomain_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = lean_array_get_size(v_xs_2575_);
v___x_2583_ = lean_nat_dec_eq(v___x_2582_, v___x_2573_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec_ref(v_codomain_2576_);
lean_dec_ref(v_es_2574_);
v___x_2584_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1);
v___x_2585_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2584_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2585_;
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2586_ = lean_unsigned_to_nat(0u);
v___x_2587_ = lean_array_fget_borrowed(v_xs_2575_, v___x_2586_);
v___x_2588_ = lean_array_to_list(v_es_2574_);
lean_inc(v___x_2587_);
v___x_2589_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2587_, v_codomain_2576_, v___x_2588_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; uint8_t v___x_2594_; lean_object* v___x_2595_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref(v___x_2589_);
v___x_2591_ = lean_mk_empty_array_with_capacity(v___x_2573_);
lean_inc(v___x_2587_);
v___x_2592_ = lean_array_push(v___x_2591_, v___x_2587_);
v___x_2593_ = 0;
v___x_2594_ = 1;
v___x_2595_ = l_Lean_Meta_mkLambdaFVars(v___x_2592_, v_a_2590_, v___x_2593_, v___x_2583_, v___x_2593_, v___x_2583_, v___x_2594_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec_ref(v___x_2592_);
return v___x_2595_;
}
else
{
return v___x_2589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed(lean_object* v___x_2596_, lean_object* v_es_2597_, lean_object* v_xs_2598_, lean_object* v_codomain_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(v___x_2596_, v_es_2597_, v_xs_2598_, v_codomain_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec_ref(v_xs_2598_);
lean_dec(v___x_2596_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND(lean_object* v_es_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
size_t v_sz_2612_; size_t v___x_2613_; lean_object* v___x_2614_; 
v_sz_2612_ = lean_array_size(v_es_2606_);
v___x_2613_ = ((size_t)0ULL);
lean_inc_ref(v_es_2606_);
v___x_2614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2612_, v___x_2613_, v_es_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2616_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref(v___x_2614_);
v___x_2616_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_a_2615_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref(v___x_2616_);
v___x_2618_ = lean_unsigned_to_nat(1u);
v___f_2619_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2619_, 0, v___x_2618_);
lean_closure_set(v___f_2619_, 1, v_es_2606_);
v___x_2620_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2621_ = 0;
v___x_2622_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_2617_, v___x_2620_, v___f_2619_, v___x_2621_, v___x_2621_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_2622_;
}
else
{
lean_dec_ref(v_es_2606_);
return v___x_2616_;
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec_ref(v_es_2606_);
v_a_2623_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2614_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2614_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___boxed(lean_object* v_es_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_es_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(lean_object* v_a_2638_, lean_object* v_domain_2639_, lean_object* v_j_2640_, lean_object* v_type_2641_, uint8_t v_isZero_2642_, lean_object* v_x_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = l_List_lengthTR___redArg(v_a_2638_);
lean_inc_ref(v_x_2643_);
v___x_2650_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2649_, v_domain_2639_, v_j_2640_, v_x_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___x_2649_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref(v___x_2650_);
v___x_2652_ = lean_unsigned_to_nat(1u);
v___x_2653_ = lean_mk_empty_array_with_capacity(v___x_2652_);
lean_inc_ref(v___x_2653_);
v___x_2654_ = lean_array_push(v___x_2653_, v_a_2651_);
v___x_2655_ = l_Lean_Meta_instantiateForall(v_type_2641_, v___x_2654_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec_ref(v___x_2654_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; uint8_t v___x_2659_; lean_object* v___x_2660_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref(v___x_2655_);
v___x_2657_ = lean_array_push(v___x_2653_, v_x_2643_);
v___x_2658_ = 1;
v___x_2659_ = 1;
v___x_2660_ = l_Lean_Meta_mkForallFVars(v___x_2657_, v_a_2656_, v_isZero_2642_, v___x_2658_, v___x_2658_, v___x_2659_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec_ref(v___x_2657_);
return v___x_2660_;
}
else
{
lean_dec_ref(v___x_2653_);
lean_dec_ref(v_x_2643_);
return v___x_2655_;
}
}
else
{
lean_dec_ref(v_x_2643_);
lean_dec_ref(v_type_2641_);
return v___x_2650_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed(lean_object* v_a_2661_, lean_object* v_domain_2662_, lean_object* v_j_2663_, lean_object* v_type_2664_, lean_object* v_isZero_2665_, lean_object* v_x_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
uint8_t v_isZero_boxed_2672_; lean_object* v_res_2673_; 
v_isZero_boxed_2672_ = lean_unbox(v_isZero_2665_);
v_res_2673_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(v_a_2661_, v_domain_2662_, v_j_2663_, v_type_2664_, v_isZero_boxed_2672_, v_x_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v_j_2663_);
lean_dec(v_a_2661_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(lean_object* v_a_2674_, lean_object* v_domain_2675_, lean_object* v_type_2676_, lean_object* v_as_2677_, lean_object* v_i_2678_, lean_object* v_j_2679_, lean_object* v_bs_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_zero_2686_; uint8_t v_isZero_2687_; 
v_zero_2686_ = lean_unsigned_to_nat(0u);
v_isZero_2687_ = lean_nat_dec_eq(v_i_2678_, v_zero_2686_);
if (v_isZero_2687_ == 1)
{
lean_object* v___x_2688_; 
lean_dec(v_j_2679_);
lean_dec(v_i_2678_);
lean_dec_ref(v_type_2676_);
lean_dec_ref(v_domain_2675_);
lean_dec(v_a_2674_);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_bs_2680_);
return v___x_2688_;
}
else
{
lean_object* v___x_2689_; lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2689_ = lean_box(v_isZero_2687_);
lean_inc_ref(v_type_2676_);
lean_inc(v_j_2679_);
lean_inc_ref(v_domain_2675_);
lean_inc(v_a_2674_);
v___f_2690_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2690_, 0, v_a_2674_);
lean_closure_set(v___f_2690_, 1, v_domain_2675_);
lean_closure_set(v___f_2690_, 2, v_j_2679_);
lean_closure_set(v___f_2690_, 3, v_type_2676_);
lean_closure_set(v___f_2690_, 4, v___x_2689_);
v___x_2691_ = lean_array_fget_borrowed(v_as_2677_, v_j_2679_);
v___x_2692_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
lean_inc(v___x_2691_);
v___x_2693_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_2692_, v___x_2691_, v___f_2690_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v_one_2695_; lean_object* v_n_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref(v___x_2693_);
v_one_2695_ = lean_unsigned_to_nat(1u);
v_n_2696_ = lean_nat_sub(v_i_2678_, v_one_2695_);
lean_dec(v_i_2678_);
v___x_2697_ = lean_nat_add(v_j_2679_, v_one_2695_);
lean_dec(v_j_2679_);
v___x_2698_ = lean_array_push(v_bs_2680_, v_a_2694_);
v_i_2678_ = v_n_2696_;
v_j_2679_ = v___x_2697_;
v_bs_2680_ = v___x_2698_;
goto _start;
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec_ref(v_bs_2680_);
lean_dec(v_j_2679_);
lean_dec(v_i_2678_);
lean_dec_ref(v_type_2676_);
lean_dec_ref(v_domain_2675_);
lean_dec(v_a_2674_);
v_a_2700_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2693_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2693_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___boxed(lean_object* v_a_2708_, lean_object* v_domain_2709_, lean_object* v_type_2710_, lean_object* v_as_2711_, lean_object* v_i_2712_, lean_object* v_j_2713_, lean_object* v_bs_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2708_, v_domain_2709_, v_type_2710_, v_as_2711_, v_i_2712_, v_j_2713_, v_bs_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v_as_2711_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType(lean_object* v_n_2721_, lean_object* v_type_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; uint8_t v___x_2749_; 
v___x_2749_ = l_Lean_Expr_isForall(v_type_2722_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
v___x_2750_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_2751_ = l_Lean_MessageData_ofExpr(v_type_2722_);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2752_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
else
{
v___y_2729_ = v_a_2723_;
v___y_2730_ = v_a_2724_;
v___y_2731_ = v_a_2725_;
v___y_2732_ = v_a_2726_;
goto v___jp_2728_;
}
v___jp_2728_:
{
lean_object* v_domain_2733_; lean_object* v___x_2734_; 
v_domain_2733_ = l_Lean_Expr_bindingDomain_x21(v_type_2722_);
lean_inc_ref(v_domain_2733_);
v___x_2734_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_2721_, v_domain_2733_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc_n(v_a_2735_, 2);
lean_dec_ref(v___x_2734_);
v___x_2736_ = lean_array_mk(v_a_2735_);
v___x_2737_ = lean_array_get_size(v___x_2736_);
v___x_2738_ = lean_unsigned_to_nat(0u);
v___x_2739_ = lean_mk_empty_array_with_capacity(v___x_2737_);
v___x_2740_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2735_, v_domain_2733_, v_type_2722_, v___x_2736_, v___x_2737_, v___x_2738_, v___x_2739_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec_ref(v___x_2736_);
return v___x_2740_;
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec_ref(v_domain_2733_);
lean_dec_ref(v_type_2722_);
v_a_2741_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2734_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2734_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType___boxed(lean_object* v_n_2762_, lean_object* v_type_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v_n_2762_, v_type_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_n_2762_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(lean_object* v_a_2770_, lean_object* v_domain_2771_, lean_object* v_type_2772_, lean_object* v_as_2773_, lean_object* v_i_2774_, lean_object* v_j_2775_, lean_object* v_inv_2776_, lean_object* v_bs_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2770_, v_domain_2771_, v_type_2772_, v_as_2773_, v_i_2774_, v_j_2775_, v_bs_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___boxed(lean_object* v_a_2784_, lean_object* v_domain_2785_, lean_object* v_type_2786_, lean_object* v_as_2787_, lean_object* v_i_2788_, lean_object* v_j_2789_, lean_object* v_inv_2790_, lean_object* v_bs_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Array_mapFinIdxM_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(v_a_2784_, v_domain_2785_, v_type_2786_, v_as_2787_, v_i_2788_, v_j_2789_, v_inv_2790_, v_bs_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_as_2787_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object* v_argsPacker_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_array_get_size(v_argsPacker_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs___boxed(lean_object* v_argsPacker_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_2800_);
lean_dec_ref(v_argsPacker_2800_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(size_t v_sz_2802_, size_t v_i_2803_, lean_object* v_bs_2804_){
_start:
{
uint8_t v___x_2805_; 
v___x_2805_ = lean_usize_dec_lt(v_i_2803_, v_sz_2802_);
if (v___x_2805_ == 0)
{
return v_bs_2804_;
}
else
{
lean_object* v_v_2806_; lean_object* v___x_2807_; lean_object* v_bs_x27_2808_; lean_object* v___x_2809_; size_t v___x_2810_; size_t v___x_2811_; lean_object* v___x_2812_; 
v_v_2806_ = lean_array_uget(v_bs_2804_, v_i_2803_);
v___x_2807_ = lean_unsigned_to_nat(0u);
v_bs_x27_2808_ = lean_array_uset(v_bs_2804_, v_i_2803_, v___x_2807_);
v___x_2809_ = lean_array_get_size(v_v_2806_);
lean_dec(v_v_2806_);
v___x_2810_ = ((size_t)1ULL);
v___x_2811_ = lean_usize_add(v_i_2803_, v___x_2810_);
v___x_2812_ = lean_array_uset(v_bs_x27_2808_, v_i_2803_, v___x_2809_);
v_i_2803_ = v___x_2811_;
v_bs_2804_ = v___x_2812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0___boxed(lean_object* v_sz_2814_, lean_object* v_i_2815_, lean_object* v_bs_2816_){
_start:
{
size_t v_sz_boxed_2817_; size_t v_i_boxed_2818_; lean_object* v_res_2819_; 
v_sz_boxed_2817_ = lean_unbox_usize(v_sz_2814_);
lean_dec(v_sz_2814_);
v_i_boxed_2818_ = lean_unbox_usize(v_i_2815_);
lean_dec(v_i_2815_);
v_res_2819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_boxed_2817_, v_i_boxed_2818_, v_bs_2816_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object* v_argsPacker_2820_){
_start:
{
size_t v_sz_2821_; size_t v___x_2822_; lean_object* v___x_2823_; 
v_sz_2821_ = lean_array_size(v_argsPacker_2820_);
v___x_2822_ = ((size_t)0ULL);
v___x_2823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_2821_, v___x_2822_, v_argsPacker_2820_);
return v___x_2823_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0(void){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Array_instInhabited(lean_box(0));
return v___x_2824_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object* v_argsPacker_2825_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2826_ = lean_array_get_size(v_argsPacker_2825_);
v___x_2827_ = lean_unsigned_to_nat(1u);
v___x_2828_ = lean_nat_dec_eq(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
return v___x_2828_;
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2829_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2830_ = lean_unsigned_to_nat(0u);
v___x_2831_ = lean_array_get_borrowed(v___x_2829_, v_argsPacker_2825_, v___x_2830_);
v___x_2832_ = lean_array_get_size(v___x_2831_);
v___x_2833_ = lean_nat_dec_eq(v___x_2832_, v___x_2827_);
return v___x_2833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_onlyOneUnary___boxed(lean_object* v_argsPacker_2834_){
_start:
{
uint8_t v_res_2835_; lean_object* v_r_2836_; 
v_res_2835_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_2834_);
lean_dec_ref(v_argsPacker_2834_);
v_r_2836_ = lean_box(v_res_2835_);
return v_r_2836_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__2(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2839_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__1));
v___x_2840_ = lean_unsigned_to_nat(2u);
v___x_2841_ = lean_unsigned_to_nat(469u);
v___x_2842_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2843_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2844_ = l_mkPanicMessageWithDecl(v___x_2843_, v___x_2842_, v___x_2841_, v___x_2840_, v___x_2839_);
return v___x_2844_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__4(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2846_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__3));
v___x_2847_ = lean_unsigned_to_nat(2u);
v___x_2848_ = lean_unsigned_to_nat(470u);
v___x_2849_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2850_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2851_ = l_mkPanicMessageWithDecl(v___x_2850_, v___x_2849_, v___x_2848_, v___x_2847_, v___x_2846_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object* v_argsPacker_2852_, lean_object* v_domain_2853_, lean_object* v_fidx_2854_, lean_object* v_args_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v___x_2861_; uint8_t v___x_2862_; 
v___x_2861_ = lean_array_get_size(v_argsPacker_2852_);
v___x_2862_ = lean_nat_dec_lt(v_fidx_2854_, v___x_2861_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec(v_fidx_2854_);
lean_dec_ref(v_domain_2853_);
v___x_2863_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__2, &l_Lean_Meta_ArgsPacker_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__2);
v___x_2864_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2863_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v___x_2865_ = lean_array_get_size(v_args_2855_);
v___x_2866_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2867_ = lean_array_get_borrowed(v___x_2866_, v_argsPacker_2852_, v_fidx_2854_);
v___x_2868_ = lean_array_get_size(v___x_2867_);
v___x_2869_ = lean_nat_dec_eq(v___x_2865_, v___x_2868_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec(v_fidx_2854_);
lean_dec_ref(v_domain_2853_);
v___x_2870_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__4, &l_Lean_Meta_ArgsPacker_pack___closed__4_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__4);
v___x_2871_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2870_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
return v___x_2871_;
}
else
{
lean_object* v___x_2872_; 
lean_inc_ref(v_domain_2853_);
v___x_2872_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v___x_2861_, v_domain_2853_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref(v___x_2872_);
v___x_2874_ = l_Lean_instInhabitedExpr;
lean_inc(v_fidx_2854_);
v___x_2875_ = l_List_get_x21Internal___redArg(v___x_2874_, v_a_2873_, v_fidx_2854_);
lean_dec(v_a_2873_);
v___x_2876_ = l_Lean_Meta_ArgsPacker_Unary_pack(v___x_2875_, v_args_2855_);
lean_dec(v___x_2875_);
v___x_2877_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2861_, v_domain_2853_, v_fidx_2854_, v___x_2876_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
lean_dec(v_fidx_2854_);
return v___x_2877_;
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec(v_fidx_2854_);
lean_dec_ref(v_domain_2853_);
v_a_2878_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2872_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2872_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack___boxed(lean_object* v_argsPacker_2886_, lean_object* v_domain_2887_, lean_object* v_fidx_2888_, lean_object* v_args_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_2886_, v_domain_2887_, v_fidx_2888_, v_args_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec_ref(v_args_2889_);
lean_dec_ref(v_argsPacker_2886_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object* v_argsPacker_2896_, lean_object* v_e_2897_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_array_get_size(v_argsPacker_2896_);
v___x_2899_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v___x_2898_, v_e_2897_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_box(0);
return v___x_2900_;
}
else
{
lean_object* v_val_2901_; lean_object* v_fst_2902_; lean_object* v_snd_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2923_; 
v_val_2901_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_val_2901_);
lean_dec_ref(v___x_2899_);
v_fst_2902_ = lean_ctor_get(v_val_2901_, 0);
v_snd_2903_ = lean_ctor_get(v_val_2901_, 1);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_val_2901_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2905_ = v_val_2901_;
v_isShared_2906_ = v_isSharedCheck_2923_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_snd_2903_);
lean_inc(v_fst_2902_);
lean_dec(v_val_2901_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2923_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2907_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2908_ = lean_array_get_borrowed(v___x_2907_, v_argsPacker_2896_, v_fst_2902_);
v___x_2909_ = lean_array_get_size(v___x_2908_);
v___x_2910_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v___x_2909_, v_snd_2903_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v___x_2911_; 
lean_del_object(v___x_2905_);
lean_dec(v_fst_2902_);
v___x_2911_ = lean_box(0);
return v___x_2911_;
}
else
{
lean_object* v_val_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2922_; 
v_val_2912_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2914_ = v___x_2910_;
v_isShared_2915_ = v_isSharedCheck_2922_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_val_2912_);
lean_dec(v___x_2910_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2922_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 1, v_val_2912_);
v___x_2917_ = v___x_2905_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_fst_2902_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_val_2912_);
v___x_2917_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2919_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2917_);
v___x_2919_ = v___x_2914_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2917_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack___boxed(lean_object* v_argsPacker_2924_, lean_object* v_e_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_2924_, v_e_2925_);
lean_dec_ref(v_argsPacker_2924_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(lean_object* v_as_2927_, lean_object* v_bs_2928_, lean_object* v_i_2929_, lean_object* v_cs_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; uint8_t v___x_2937_; 
v___x_2936_ = lean_array_get_size(v_as_2927_);
v___x_2937_ = lean_nat_dec_lt(v_i_2929_, v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; 
lean_dec(v_i_2929_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v_cs_2930_);
return v___x_2938_;
}
else
{
lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2939_ = lean_array_get_size(v_bs_2928_);
v___x_2940_ = lean_nat_dec_lt(v_i_2929_, v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; 
lean_dec(v_i_2929_);
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_cs_2930_);
return v___x_2941_;
}
else
{
lean_object* v_a_2942_; lean_object* v_b_2943_; lean_object* v___x_2944_; 
v_a_2942_ = lean_array_fget_borrowed(v_as_2927_, v_i_2929_);
v_b_2943_ = lean_array_fget_borrowed(v_bs_2928_, v_i_2929_);
lean_inc(v_b_2943_);
lean_inc(v_a_2942_);
v___x_2944_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_a_2942_, v_b_2943_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2944_);
v___x_2946_ = lean_unsigned_to_nat(1u);
v___x_2947_ = lean_nat_add(v_i_2929_, v___x_2946_);
lean_dec(v_i_2929_);
v___x_2948_ = lean_array_push(v_cs_2930_, v_a_2945_);
v_i_2929_ = v___x_2947_;
v_cs_2930_ = v___x_2948_;
goto _start;
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec_ref(v_cs_2930_);
lean_dec(v_i_2929_);
v_a_2950_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2944_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2944_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0___boxed(lean_object* v_as_2958_, lean_object* v_bs_2959_, lean_object* v_i_2960_, lean_object* v_cs_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_as_2958_, v_bs_2959_, v_i_2960_, v_cs_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec_ref(v_bs_2959_);
lean_dec_ref(v_as_2958_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object* v_argsPacker_2968_, lean_object* v_types_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2975_ = lean_unsigned_to_nat(0u);
v___x_2976_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_2977_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_argsPacker_2968_, v_types_2969_, v___x_2975_, v___x_2976_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref(v___x_2977_);
v___x_2979_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2978_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
return v___x_2979_;
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
v_a_2980_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2977_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2977_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType___boxed(lean_object* v_argsPacker_2988_, lean_object* v_types_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2988_, v_types_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec_ref(v_types_2989_);
lean_dec_ref(v_argsPacker_2988_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(lean_object* v_as_2996_, lean_object* v_bs_2997_, lean_object* v_i_2998_, lean_object* v_cs_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = lean_array_get_size(v_as_2996_);
v___x_3006_ = lean_nat_dec_lt(v_i_2998_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; 
lean_dec(v_i_2998_);
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_cs_2999_);
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3008_ = lean_array_get_size(v_bs_2997_);
v___x_3009_ = lean_nat_dec_lt(v_i_2998_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; 
lean_dec(v_i_2998_);
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v_cs_2999_);
return v___x_3010_;
}
else
{
lean_object* v_a_3011_; lean_object* v_b_3012_; lean_object* v___x_3013_; 
v_a_3011_ = lean_array_fget_borrowed(v_as_2996_, v_i_2998_);
v_b_3012_ = lean_array_fget_borrowed(v_bs_2997_, v_i_2998_);
lean_inc(v_b_3012_);
lean_inc(v_a_3011_);
v___x_3013_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_a_3011_, v_b_3012_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref(v___x_3013_);
v___x_3015_ = lean_unsigned_to_nat(1u);
v___x_3016_ = lean_nat_add(v_i_2998_, v___x_3015_);
lean_dec(v_i_2998_);
v___x_3017_ = lean_array_push(v_cs_2999_, v_a_3014_);
v_i_2998_ = v___x_3016_;
v_cs_2999_ = v___x_3017_;
goto _start;
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec_ref(v_cs_2999_);
lean_dec(v_i_2998_);
v_a_3019_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3013_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3013_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0___boxed(lean_object* v_as_3027_, lean_object* v_bs_3028_, lean_object* v_i_3029_, lean_object* v_cs_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_as_3027_, v_bs_3028_, v_i_3029_, v_cs_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec_ref(v_bs_3028_);
lean_dec_ref(v_as_3027_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object* v_argsPacker_3037_, lean_object* v_es_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = lean_unsigned_to_nat(0u);
v___x_3045_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3046_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3037_, v_es_3038_, v___x_3044_, v___x_3045_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3048_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref(v___x_3046_);
v___x_3048_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_a_3047_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
return v___x_3048_;
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
v_a_3049_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3046_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3046_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry___boxed(lean_object* v_argsPacker_3057_, lean_object* v_es_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_3057_, v_es_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec_ref(v_es_3058_);
lean_dec_ref(v_argsPacker_3057_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType(lean_object* v_argsPacker_3065_, lean_object* v_resultType_3066_, lean_object* v_es_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3075_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3065_, v_es_3067_, v___x_3073_, v___x_3074_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3077_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref(v___x_3075_);
v___x_3077_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_3066_, v_a_3076_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
return v___x_3077_;
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec_ref(v_resultType_3066_);
v_a_3078_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3075_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3075_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType___boxed(lean_object* v_argsPacker_3086_, lean_object* v_resultType_3087_, lean_object* v_es_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3086_, v_resultType_3087_, v_es_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec_ref(v_es_3088_);
lean_dec_ref(v_argsPacker_3086_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object* v_argsPacker_3095_, lean_object* v_es_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_unsigned_to_nat(0u);
v___x_3103_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3104_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3095_, v_es_3096_, v___x_3102_, v___x_3103_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3106_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref(v___x_3104_);
v___x_3106_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_a_3105_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
return v___x_3106_;
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
v_a_3107_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3104_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3104_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND___boxed(lean_object* v_argsPacker_3115_, lean_object* v_es_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_3115_, v_es_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
lean_dec(v_a_3120_);
lean_dec_ref(v_a_3119_);
lean_dec(v_a_3118_);
lean_dec_ref(v_a_3117_);
lean_dec_ref(v_es_3116_);
lean_dec_ref(v_argsPacker_3115_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(lean_object* v_msg_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___f_3129_; lean_object* v___x_1078__overap_3130_; lean_object* v___x_3131_; 
v___f_3129_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_1078__overap_3130_ = lean_panic_fn_borrowed(v___f_3129_, v_msg_3123_);
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3126_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3124_);
v___x_3131_ = lean_apply_5(v___x_1078__overap_3130_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, lean_box(0));
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0___boxed(lean_object* v_msg_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v_msg_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0(lean_object* v_a_3139_, lean_object* v___x_3140_, lean_object* v_i_3141_, lean_object* v_e_3142_, lean_object* v_x_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = l_List_lengthTR___redArg(v_a_3139_);
lean_inc_ref(v_x_3143_);
v___x_3150_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_3149_, v___x_3140_, v_i_3141_, v_x_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec(v___x_3149_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; uint8_t v___x_3158_; uint8_t v___x_3159_; lean_object* v___x_3160_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref(v___x_3150_);
v___x_3152_ = lean_unsigned_to_nat(1u);
v___x_3153_ = lean_mk_empty_array_with_capacity(v___x_3152_);
lean_inc_ref(v___x_3153_);
v___x_3154_ = lean_array_push(v___x_3153_, v_x_3143_);
v___x_3155_ = lean_array_push(v___x_3153_, v_a_3151_);
v___x_3156_ = l_Lean_Expr_beta(v_e_3142_, v___x_3155_);
v___x_3157_ = 0;
v___x_3158_ = 1;
v___x_3159_ = 1;
v___x_3160_ = l_Lean_Meta_mkLambdaFVars(v___x_3154_, v___x_3156_, v___x_3157_, v___x_3158_, v___x_3157_, v___x_3158_, v___x_3159_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec_ref(v___x_3154_);
return v___x_3160_;
}
else
{
lean_dec_ref(v_x_3143_);
lean_dec_ref(v_e_3142_);
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed(lean_object* v_a_3161_, lean_object* v___x_3162_, lean_object* v_i_3163_, lean_object* v_e_3164_, lean_object* v_x_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_Meta_ArgsPacker_curryProj___lam__0(v_a_3161_, v___x_3162_, v_i_3163_, v_e_3164_, v_x_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v_i_3163_);
lean_dec(v_a_3161_);
return v_res_3171_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1(void){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__0));
v___x_3174_ = l_Lean_stringToMessageData(v___x_3173_);
return v___x_3174_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3177_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__3));
v___x_3178_ = lean_unsigned_to_nat(4u);
v___x_3179_ = lean_unsigned_to_nat(535u);
v___x_3180_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__2));
v___x_3181_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_3182_ = l_mkPanicMessageWithDecl(v___x_3181_, v___x_3180_, v___x_3179_, v___x_3178_, v___x_3177_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object* v_argsPacker_3183_, lean_object* v_e_3184_, lean_object* v_i_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v___x_3191_; 
lean_inc(v_a_3189_);
lean_inc_ref(v_a_3188_);
lean_inc(v_a_3187_);
lean_inc_ref(v_a_3186_);
lean_inc_ref(v_e_3184_);
v___x_3191_ = lean_infer_type(v_e_3184_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3193_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref(v___x_3191_);
lean_inc(v_a_3189_);
lean_inc_ref(v_a_3188_);
lean_inc(v_a_3187_);
lean_inc_ref(v_a_3186_);
v___x_3193_ = lean_whnf(v_a_3192_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v_n_3210_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; uint8_t v___x_3240_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref(v___x_3193_);
v___x_3195_ = l_Lean_instInhabitedExpr;
v___x_3196_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v_n_3210_ = lean_array_get_size(v_argsPacker_3183_);
v___x_3240_ = l_Lean_Expr_isForall(v_a_3194_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__4, &l_Lean_Meta_ArgsPacker_curryProj___closed__4_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4);
v___x_3242_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v___x_3241_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_dec_ref(v___x_3242_);
v___y_3212_ = v_a_3186_;
v___y_3213_ = v_a_3187_;
v___y_3214_ = v_a_3188_;
v___y_3215_ = v_a_3189_;
goto v___jp_3211_;
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec(v_a_3194_);
lean_dec(v_i_3185_);
lean_dec_ref(v_e_3184_);
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
else
{
v___y_3212_ = v_a_3186_;
v___y_3213_ = v_a_3187_;
v___y_3214_ = v_a_3188_;
v___y_3215_ = v_a_3189_;
goto v___jp_3211_;
}
v___jp_3197_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_inc(v_i_3185_);
v___x_3204_ = l_List_get_x21Internal___redArg(v___x_3195_, v___y_3199_, v_i_3185_);
lean_dec(v___y_3199_);
v___x_3205_ = l_Lean_Expr_bindingName_x21(v_a_3194_);
lean_dec(v_a_3194_);
v___x_3206_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3205_, v___x_3204_, v___y_3198_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
lean_dec_ref(v___x_3206_);
v___x_3208_ = lean_array_get_borrowed(v___x_3196_, v_argsPacker_3183_, v_i_3185_);
lean_dec(v_i_3185_);
lean_inc(v___x_3208_);
v___x_3209_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v___x_3208_, v_a_3207_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
return v___x_3209_;
}
else
{
lean_dec(v_i_3185_);
return v___x_3206_;
}
}
v___jp_3211_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = l_Lean_Expr_bindingDomain_x21(v_a_3194_);
lean_inc_ref(v___x_3216_);
v___x_3217_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_3210_, v___x_3216_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc_n(v_a_3218_, 2);
lean_dec_ref(v___x_3217_);
lean_inc(v_i_3185_);
v___f_3219_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3219_, 0, v_a_3218_);
lean_closure_set(v___f_3219_, 1, v___x_3216_);
lean_closure_set(v___f_3219_, 2, v_i_3185_);
lean_closure_set(v___f_3219_, 3, v_e_3184_);
v___x_3220_ = l_List_lengthTR___redArg(v_a_3218_);
v___x_3221_ = lean_nat_dec_lt(v_i_3185_, v___x_3220_);
lean_dec(v___x_3220_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref(v___f_3219_);
lean_dec(v_a_3218_);
lean_dec(v_a_3194_);
lean_dec(v_i_3185_);
v___x_3222_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__1, &l_Lean_Meta_ArgsPacker_curryProj___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1);
v___x_3223_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3222_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
else
{
v___y_3198_ = v___f_3219_;
v___y_3199_ = v_a_3218_;
v___y_3200_ = v___y_3212_;
v___y_3201_ = v___y_3213_;
v___y_3202_ = v___y_3214_;
v___y_3203_ = v___y_3215_;
goto v___jp_3197_;
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v___x_3216_);
lean_dec(v_a_3194_);
lean_dec(v_i_3185_);
lean_dec_ref(v_e_3184_);
v_a_3232_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3217_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3217_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
}
else
{
lean_dec(v_i_3185_);
lean_dec_ref(v_e_3184_);
return v___x_3193_;
}
}
else
{
lean_dec(v_i_3185_);
lean_dec_ref(v_e_3184_);
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___boxed(lean_object* v_argsPacker_3251_, lean_object* v_e_3252_, lean_object* v_i_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3251_, v_e_3252_, v_i_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
lean_dec(v_a_3257_);
lean_dec_ref(v_a_3256_);
lean_dec(v_a_3255_);
lean_dec_ref(v_a_3254_);
lean_dec_ref(v_argsPacker_3251_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(lean_object* v_as_3260_, lean_object* v_bs_3261_, lean_object* v_i_3262_, lean_object* v_cs_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3269_ = lean_array_get_size(v_as_3260_);
v___x_3270_ = lean_nat_dec_lt(v_i_3262_, v___x_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; 
lean_dec(v_i_3262_);
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_cs_3263_);
return v___x_3271_;
}
else
{
lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3272_ = lean_array_get_size(v_bs_3261_);
v___x_3273_ = lean_nat_dec_lt(v_i_3262_, v___x_3272_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
lean_dec(v_i_3262_);
v___x_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3274_, 0, v_cs_3263_);
return v___x_3274_;
}
else
{
lean_object* v_a_3275_; lean_object* v_b_3276_; lean_object* v___x_3277_; 
v_a_3275_ = lean_array_fget_borrowed(v_as_3260_, v_i_3262_);
v_b_3276_ = lean_array_fget_borrowed(v_bs_3261_, v_i_3262_);
lean_inc(v_b_3276_);
lean_inc(v_a_3275_);
v___x_3277_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_a_3275_, v_b_3276_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref(v___x_3277_);
v___x_3279_ = lean_unsigned_to_nat(1u);
v___x_3280_ = lean_nat_add(v_i_3262_, v___x_3279_);
lean_dec(v_i_3262_);
v___x_3281_ = lean_array_push(v_cs_3263_, v_a_3278_);
v_i_3262_ = v___x_3280_;
v_cs_3263_ = v___x_3281_;
goto _start;
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec_ref(v_cs_3263_);
lean_dec(v_i_3262_);
v_a_3283_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3277_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3277_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0___boxed(lean_object* v_as_3291_, lean_object* v_bs_3292_, lean_object* v_i_3293_, lean_object* v_cs_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_as_3291_, v_bs_3292_, v_i_3293_, v_cs_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec_ref(v_bs_3292_);
lean_dec_ref(v_as_3291_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType(lean_object* v_argsPacker_3301_, lean_object* v_t_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = lean_array_get_size(v_argsPacker_3301_);
v___x_3309_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v___x_3308_, v_t_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3310_);
lean_dec_ref(v___x_3309_);
v___x_3311_ = lean_unsigned_to_nat(0u);
v___x_3312_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3313_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_argsPacker_3301_, v_a_3310_, v___x_3311_, v___x_3312_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
lean_dec(v_a_3310_);
return v___x_3313_;
}
else
{
return v___x_3309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType___boxed(lean_object* v_argsPacker_3314_, lean_object* v_t_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3314_, v_t_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
lean_dec(v_a_3319_);
lean_dec_ref(v_a_3318_);
lean_dec(v_a_3317_);
lean_dec_ref(v_a_3316_);
lean_dec_ref(v_argsPacker_3314_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(lean_object* v_upperBound_3322_, lean_object* v_argsPacker_3323_, lean_object* v_e_3324_, lean_object* v_a_3325_, lean_object* v_b_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
uint8_t v___x_3332_; 
v___x_3332_ = lean_nat_dec_lt(v_a_3325_, v_upperBound_3322_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; 
lean_dec(v_a_3325_);
lean_dec_ref(v_e_3324_);
v___x_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3333_, 0, v_b_3326_);
return v___x_3333_;
}
else
{
lean_object* v___x_3334_; 
lean_inc(v_a_3325_);
lean_inc_ref(v_e_3324_);
v___x_3334_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3323_, v_e_3324_, v_a_3325_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = lean_array_push(v_b_3326_, v_a_3335_);
v___x_3337_ = lean_unsigned_to_nat(1u);
v___x_3338_ = lean_nat_add(v_a_3325_, v___x_3337_);
lean_dec(v_a_3325_);
v_a_3325_ = v___x_3338_;
v_b_3326_ = v___x_3336_;
goto _start;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec_ref(v_b_3326_);
lean_dec(v_a_3325_);
lean_dec_ref(v_e_3324_);
v_a_3340_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3334_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3334_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg___boxed(lean_object* v_upperBound_3348_, lean_object* v_argsPacker_3349_, lean_object* v_e_3350_, lean_object* v_a_3351_, lean_object* v_b_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3348_, v_argsPacker_3349_, v_e_3350_, v_a_3351_, v_b_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec_ref(v_argsPacker_3349_);
lean_dec(v_upperBound_3348_);
return v_res_3358_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curry___closed__0(void){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = lean_unsigned_to_nat(0u);
v___x_3360_ = l_Lean_Level_ofNat(v___x_3359_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry(lean_object* v_argsPacker_3361_, lean_object* v_e_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v_es_3370_; lean_object* v___x_3371_; 
v___x_3368_ = lean_array_get_size(v_argsPacker_3361_);
v___x_3369_ = lean_unsigned_to_nat(0u);
v_es_3370_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3371_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v___x_3368_, v_argsPacker_3361_, v_e_3362_, v___x_3369_, v_es_3370_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3372_);
lean_dec_ref(v___x_3371_);
v___x_3373_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curry___closed__0, &l_Lean_Meta_ArgsPacker_curry___closed__0_once, _init_l_Lean_Meta_ArgsPacker_curry___closed__0);
v___x_3374_ = l_Lean_Meta_PProdN_mk(v___x_3373_, v_a_3372_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
return v___x_3374_;
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
v_a_3375_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3371_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3371_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry___boxed(lean_object* v_argsPacker_3383_, lean_object* v_e_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_Meta_ArgsPacker_curry(v_argsPacker_3383_, v_e_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
lean_dec_ref(v_argsPacker_3383_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(lean_object* v_upperBound_3391_, lean_object* v_argsPacker_3392_, lean_object* v_e_3393_, lean_object* v_inst_3394_, lean_object* v_R_3395_, lean_object* v_a_3396_, lean_object* v_b_3397_, lean_object* v_c_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3391_, v_argsPacker_3392_, v_e_3393_, v_a_3396_, v_b_3397_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___boxed(lean_object* v_upperBound_3405_, lean_object* v_argsPacker_3406_, lean_object* v_e_3407_, lean_object* v_inst_3408_, lean_object* v_R_3409_, lean_object* v_a_3410_, lean_object* v_b_3411_, lean_object* v_c_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(v_upperBound_3405_, v_argsPacker_3406_, v_e_3407_, v_inst_3408_, v_R_3409_, v_a_3410_, v_b_3411_, v_c_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec_ref(v_argsPacker_3406_);
lean_dec(v_upperBound_3405_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed(lean_object* v_a_3419_, lean_object* v_argsPacker_3420_, lean_object* v_name_3421_, lean_object* v_k_3422_, lean_object* v_tail_3423_, lean_object* v_x_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(v_a_3419_, v_argsPacker_3420_, v_name_3421_, v_k_3422_, v_tail_3423_, v_x_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(lean_object* v_argsPacker_3431_, lean_object* v_name_3432_, lean_object* v_k_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
if (lean_obj_tag(v_a_3434_) == 0)
{
lean_object* v___x_3441_; 
lean_dec(v_name_3432_);
lean_dec_ref(v_argsPacker_3431_);
lean_inc(v_a_3439_);
lean_inc_ref(v_a_3438_);
lean_inc(v_a_3437_);
lean_inc_ref(v_a_3436_);
v___x_3441_ = lean_apply_6(v_k_3433_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, lean_box(0));
return v___x_3441_;
}
else
{
lean_object* v_head_3442_; lean_object* v_tail_3443_; lean_object* v___f_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_head_3442_ = lean_ctor_get(v_a_3434_, 0);
lean_inc(v_head_3442_);
v_tail_3443_ = lean_ctor_get(v_a_3434_, 1);
lean_inc(v_tail_3443_);
lean_dec_ref(v_a_3434_);
lean_inc(v_name_3432_);
lean_inc_ref(v_argsPacker_3431_);
lean_inc_ref(v_a_3435_);
v___f_3444_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3444_, 0, v_a_3435_);
lean_closure_set(v___f_3444_, 1, v_argsPacker_3431_);
lean_closure_set(v___f_3444_, 2, v_name_3432_);
lean_closure_set(v___f_3444_, 3, v_k_3433_);
lean_closure_set(v___f_3444_, 4, v_tail_3443_);
v___x_3445_ = lean_array_get_size(v_argsPacker_3431_);
lean_dec_ref(v_argsPacker_3431_);
v___x_3446_ = lean_unsigned_to_nat(1u);
v___x_3447_ = lean_nat_dec_eq(v___x_3445_, v___x_3446_);
if (v___x_3447_ == 0)
{
uint8_t v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3448_ = 1;
v___x_3449_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3432_, v___x_3448_);
v___x_3450_ = lean_array_get_size(v_a_3435_);
lean_dec_ref(v_a_3435_);
v___x_3451_ = lean_nat_add(v___x_3450_, v___x_3446_);
v___x_3452_ = l_Nat_reprFast(v___x_3451_);
v___x_3453_ = lean_string_append(v___x_3449_, v___x_3452_);
lean_dec_ref(v___x_3452_);
v___x_3454_ = lean_box(0);
v___x_3455_ = l_Lean_Name_str___override(v___x_3454_, v___x_3453_);
v___x_3456_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3455_, v_head_3442_, v___f_3444_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
return v___x_3456_;
}
else
{
lean_object* v___x_3457_; 
lean_dec_ref(v_a_3435_);
v___x_3457_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_3432_, v_head_3442_, v___f_3444_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
return v___x_3457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(lean_object* v_a_3458_, lean_object* v_argsPacker_3459_, lean_object* v_name_3460_, lean_object* v_k_3461_, lean_object* v_tail_3462_, lean_object* v_x_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = lean_array_push(v_a_3458_, v_x_3463_);
v___x_3470_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3459_, v_name_3460_, v_k_3461_, v_tail_3462_, v___x_3469_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___boxed(lean_object* v_argsPacker_3471_, lean_object* v_name_3472_, lean_object* v_k_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3471_, v_name_3472_, v_k_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(lean_object* v_00_u03b1_3482_, lean_object* v_argsPacker_3483_, lean_object* v_name_3484_, lean_object* v_k_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3483_, v_name_3484_, v_k_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___boxed(lean_object* v_00_u03b1_3494_, lean_object* v_argsPacker_3495_, lean_object* v_name_3496_, lean_object* v_k_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(v_00_u03b1_3494_, v_argsPacker_3495_, v_name_3496_, v_k_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(lean_object* v_argsPacker_3506_, lean_object* v_name_3507_, lean_object* v_type_3508_, lean_object* v_k_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3506_, v_type_3508_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref(v___x_3515_);
v___x_3517_ = lean_array_to_list(v_a_3516_);
v___x_3518_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3519_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3506_, v_name_3507_, v_k_3509_, v___x_3517_, v___x_3518_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
return v___x_3519_;
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v_k_3509_);
lean_dec(v_name_3507_);
lean_dec_ref(v_argsPacker_3506_);
v_a_3520_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3515_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3515_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg___boxed(lean_object* v_argsPacker_3528_, lean_object* v_name_3529_, lean_object* v_type_3530_, lean_object* v_k_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3528_, v_name_3529_, v_type_3530_, v_k_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(lean_object* v_00_u03b1_3538_, lean_object* v_argsPacker_3539_, lean_object* v_name_3540_, lean_object* v_type_3541_, lean_object* v_k_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3539_, v_name_3540_, v_type_3541_, v_k_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___boxed(lean_object* v_00_u03b1_3549_, lean_object* v_argsPacker_3550_, lean_object* v_name_3551_, lean_object* v_type_3552_, lean_object* v_k_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(v_00_u03b1_3549_, v_argsPacker_3550_, v_name_3551_, v_type_3552_, v_k_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
lean_dec(v_a_3555_);
lean_dec_ref(v_a_3554_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(lean_object* v_argsPacker_3560_, lean_object* v_packedMotiveType_3561_, lean_object* v_type_3562_, lean_object* v_value_3563_, lean_object* v_k_3564_, lean_object* v_motives_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3560_, v_packedMotiveType_3561_, v_motives_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc_n(v_a_3572_, 2);
lean_dec_ref(v___x_3571_);
v___x_3573_ = lean_unsigned_to_nat(1u);
v___x_3574_ = lean_mk_empty_array_with_capacity(v___x_3573_);
v___x_3575_ = lean_array_push(v___x_3574_, v_a_3572_);
v___x_3576_ = l_Lean_Meta_instantiateForall(v_type_3562_, v___x_3575_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec_ref(v___x_3575_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref(v___x_3576_);
v___x_3578_ = l_Lean_Expr_app___override(v_value_3563_, v_a_3572_);
lean_inc(v___y_3569_);
lean_inc_ref(v___y_3568_);
lean_inc(v___y_3567_);
lean_inc_ref(v___y_3566_);
v___x_3579_ = lean_apply_8(v_k_3564_, v_motives_3565_, v___x_3578_, v_a_3577_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, lean_box(0));
return v___x_3579_;
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec(v_a_3572_);
lean_dec_ref(v_motives_3565_);
lean_dec_ref(v_k_3564_);
lean_dec_ref(v_value_3563_);
v_a_3580_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3576_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3576_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v_motives_3565_);
lean_dec_ref(v_k_3564_);
lean_dec_ref(v_value_3563_);
lean_dec_ref(v_type_3562_);
v_a_3588_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3571_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3571_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed(lean_object* v_argsPacker_3596_, lean_object* v_packedMotiveType_3597_, lean_object* v_type_3598_, lean_object* v_value_3599_, lean_object* v_k_3600_, lean_object* v_motives_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(v_argsPacker_3596_, v_packedMotiveType_3597_, v_type_3598_, v_value_3599_, v_k_3600_, v_motives_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v_argsPacker_3596_);
return v_res_3607_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1(void){
_start:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0));
v___x_3610_ = l_Lean_stringToMessageData(v___x_3609_);
return v___x_3610_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2));
v___x_3613_ = l_Lean_stringToMessageData(v___x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg(lean_object* v_argsPacker_3614_, lean_object* v_value_3615_, lean_object* v_type_3616_, lean_object* v_k_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; uint8_t v___x_3652_; 
v___x_3652_ = l_Lean_Expr_isForall(v_type_3616_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_dec_ref(v_k_3617_);
lean_dec_ref(v_value_3615_);
lean_dec_ref(v_argsPacker_3614_);
v___x_3653_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3);
v___x_3654_ = l_Lean_MessageData_ofExpr(v_type_3616_);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3655_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_);
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3656_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3656_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
else
{
v___y_3633_ = v_a_3618_;
v___y_3634_ = v_a_3619_;
v___y_3635_ = v_a_3620_;
v___y_3636_ = v_a_3621_;
goto v___jp_3632_;
}
v___jp_3623_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = l_Lean_Expr_bindingName_x21(v_type_3616_);
lean_dec_ref(v_type_3616_);
v___x_3631_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3614_, v___x_3630_, v___y_3625_, v___y_3624_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
return v___x_3631_;
}
v___jp_3632_:
{
lean_object* v_packedMotiveType_3637_; lean_object* v___f_3638_; uint8_t v___x_3639_; 
v_packedMotiveType_3637_ = l_Lean_Expr_bindingDomain_x21(v_type_3616_);
lean_inc_ref(v_type_3616_);
lean_inc_ref(v_packedMotiveType_3637_);
lean_inc_ref(v_argsPacker_3614_);
v___f_3638_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3638_, 0, v_argsPacker_3614_);
lean_closure_set(v___f_3638_, 1, v_packedMotiveType_3637_);
lean_closure_set(v___f_3638_, 2, v_type_3616_);
lean_closure_set(v___f_3638_, 3, v_value_3615_);
lean_closure_set(v___f_3638_, 4, v_k_3617_);
v___x_3639_ = l_Lean_Expr_isForall(v_packedMotiveType_3637_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
lean_dec_ref(v___f_3638_);
lean_dec_ref(v_type_3616_);
lean_dec_ref(v_argsPacker_3614_);
v___x_3640_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1);
v___x_3641_ = l_Lean_indentExpr(v_packedMotiveType_3637_);
v___x_3642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3640_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3642_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
else
{
v___y_3624_ = v___f_3638_;
v___y_3625_ = v_packedMotiveType_3637_;
v___y_3626_ = v___y_3633_;
v___y_3627_ = v___y_3634_;
v___y_3628_ = v___y_3635_;
v___y_3629_ = v___y_3636_;
goto v___jp_3623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___boxed(lean_object* v_argsPacker_3665_, lean_object* v_value_3666_, lean_object* v_type_3667_, lean_object* v_k_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3665_, v_value_3666_, v_type_3667_, v_k_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam(lean_object* v_00_u03b1_3675_, lean_object* v_argsPacker_3676_, lean_object* v_value_3677_, lean_object* v_type_3678_, lean_object* v_k_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3676_, v_value_3677_, v_type_3678_, v_k_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___boxed(lean_object* v_00_u03b1_3686_, lean_object* v_argsPacker_3687_, lean_object* v_value_3688_, lean_object* v_type_3689_, lean_object* v_k_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lean_Meta_ArgsPacker_curryParam(v_00_u03b1_3686_, v_argsPacker_3687_, v_value_3688_, v_type_3689_, v_k_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
return v_res_3696_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ArgsPacker_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ArgsPacker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
