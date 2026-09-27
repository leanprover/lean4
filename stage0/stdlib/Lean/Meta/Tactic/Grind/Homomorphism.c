// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Homomorphism
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.Homo public import Lean.Meta.Sym.Simp.SimpM import Init.Grind.Homo.Extra import Lean.Meta.NatInstTesters import Lean.Meta.Sym.LitValues import Lean.Meta.Tactic.Grind.Diseq import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.EvalGround
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_Grind_registerSolverExtension___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Nat_mkInstHDiv;
extern lean_object* l_Lean_Nat_mkInstHMod;
lean_object* l_Lean_mkNatMul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAndNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkHomoPredInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "hom"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 254, 229, 211, 186, 100, 148, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Homomorphism"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 40, 35, 7, 90, 245, 98, 206)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(173, 33, 165, 246, 19, 142, 127, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 152, 96, 139, 215, 165, 231, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 88, 147, 154, 131, 237, 72, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(142, 150, 207, 215, 57, 47, 128, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Homo"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 97, 15, 175, 123, 219, 173, 123)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 91, 45, 194, 122, 52, 201, 113)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 55, 21, 223, 53, 32, 164, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(29, 81, 60, 28, 4, 71, 132, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 152, 143, 143, 254, 232, 99, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(204, 80, 221, 141, 17, 69, 156, 211)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 244, 64, 195, 64, 183, 126, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 30, 194, 254, 212, 12, 37, 229)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pred"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 254, 229, 211, 186, 100, 148, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 94, 180, 116, 28, 106, 148, 117)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_homExt;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 205, 8, 181, 48, 134, 168, 175)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 171, 107, 112, 94, 43, 106, 200)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "and_eq_div_mod_mul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(172, 213, 253, 107, 196, 179, 180, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "ones_zeros_and_eq_div_mod_mul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(200, 71, 30, 242, 231, 136, 113, 27)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "and_eq_mod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(41, 150, 170, 114, 144, 96, 66, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ones_and_eq_mod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(153, 240, 108, 217, 24, 169, 196, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\n===>\n"};
static const lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Homo_processNewDiseq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Homo_processNewDiseq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Homo_processNewDiseq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Homo_processNewDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Homo_processNewDiseq___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Homo_internalize___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Homo_processNewEq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Homo_processNewDiseq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_unsigned_to_nat(3754153130u);
v___x_70_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_71_ = l_Lean_Name_num___override(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_74_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_);
v___x_75_ = l_Lean_Name_str___override(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_78_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_);
v___x_79_ = l_Lean_Name_str___override(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(2u);
v___x_81_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_);
v___x_82_ = l_Lean_Name_num___override(v___x_81_, v___x_80_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_85_ = 0;
v___x_86_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_);
v___x_87_ = l_Lean_registerTraceClass(v___x_84_, v___x_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2____boxed(lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_();
return v_res_89_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_unsigned_to_nat(2531264644u);
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_97_ = l_Lean_Name_num___override(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_99_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_100_ = l_Lean_Name_str___override(v___x_99_, v___x_98_);
return v___x_100_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_102_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_103_ = l_Lean_Name_str___override(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(2u);
v___x_105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_106_ = l_Lean_Name_num___override(v___x_105_, v___x_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_));
v___x_109_ = 1;
v___x_110_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_111_ = l_Lean_registerTraceClass(v___x_108_, v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2____boxed(lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_();
return v_res_113_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_114_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg(){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___dummy_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg();
return v_res_120_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg();
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(lean_object* v___x_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object* v___x_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(v___x_127_);
return v_res_129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_132_ = l_Lean_NameSet_empty;
v___x_133_ = lean_box(1);
v___x_134_ = 0;
v___x_135_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0);
v___x_136_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_137_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
lean_ctor_set(v___x_137_, 2, v___x_136_);
lean_ctor_set(v___x_137_, 3, v___x_133_);
lean_ctor_set(v___x_137_, 4, v___x_132_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*5, v___x_134_);
return v___x_137_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_138_; lean_object* v___f_139_; 
v___x_138_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___f_139_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_139_, 0, v___x_138_);
return v___f_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; 
v___f_141_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_142_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_();
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0(uint8_t v___x_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_s_149_){
_start:
{
lean_object* v_cache_150_; lean_object* v_internalized_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_cache_150_ = lean_ctor_get(v_s_149_, 0);
v_internalized_151_ = lean_ctor_get(v_s_149_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_s_149_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; lean_object* v_unused_160_; lean_object* v_unused_161_; 
v_unused_159_ = lean_ctor_get(v_s_149_, 4);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_s_149_, 3);
lean_dec(v_unused_160_);
v_unused_161_ = lean_ctor_get(v_s_149_, 2);
lean_dec(v_unused_161_);
v___x_153_ = v_s_149_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_internalized_151_);
lean_inc(v_cache_150_);
lean_dec(v_s_149_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v_a_148_);
lean_ctor_set(v___x_153_, 3, v_a_147_);
lean_ctor_set(v___x_153_, 2, v_a_146_);
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_cache_150_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_internalized_151_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_a_146_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v_a_147_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v_a_148_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*5, v___x_145_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0___boxed(lean_object* v___x_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_s_166_){
_start:
{
uint8_t v___x_4129__boxed_167_; lean_object* v_res_168_; 
v___x_4129__boxed_167_ = lean_unbox(v___x_162_);
v_res_168_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0(v___x_4129__boxed_167_, v_a_163_, v_a_164_, v_a_165_, v_s_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_174_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_173_, v_a_169_, v_a_170_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_218_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_218_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_218_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_218_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
uint8_t v_initialized_179_; 
v_initialized_179_ = lean_ctor_get_uint8(v_a_175_, sizeof(void*)*5);
lean_dec(v_a_175_);
if (v_initialized_179_ == 0)
{
uint8_t v___x_180_; lean_object* v___x_181_; 
lean_del_object(v___x_177_);
v___x_180_ = 1;
v___x_181_ = l_Lean_Meta_Grind_getHomoTheorems___redArg(v_a_171_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_183_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
v___x_183_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_171_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_185_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
v___x_185_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_171_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; lean_object* v___f_188_; lean_object* v___x_189_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v___x_187_ = lean_box(v___x_180_);
v___f_188_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_188_, 0, v___x_187_);
lean_closure_set(v___f_188_, 1, v_a_182_);
lean_closure_set(v___f_188_, 2, v_a_184_);
lean_closure_set(v___f_188_, 3, v_a_186_);
v___x_189_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_173_, v___f_188_, v_a_169_);
return v___x_189_;
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec(v_a_184_);
lean_dec(v_a_182_);
v_a_190_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_185_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_185_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec(v_a_182_);
v_a_198_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_183_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_183_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_a_206_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_181_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_181_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_box(0);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_214_);
v___x_216_ = v___x_177_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
v_a_219_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_174_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_174_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___boxed(lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_227_, v_a_228_, v_a_229_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init(lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_232_, v_a_240_, v_a_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___boxed(lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init(v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec(v_a_244_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_256_, v_a_257_, v_a_258_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec_ref_known(v___x_260_, 1);
v___x_261_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_262_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_261_, v_a_256_, v_a_257_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_271_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_271_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v_thms_267_; lean_object* v___x_269_; 
v_thms_267_ = lean_ctor_get(v_a_263_, 2);
lean_inc_ref(v_thms_267_);
lean_dec(v_a_263_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v_thms_267_);
v___x_269_ = v___x_265_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_thms_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
v_a_272_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_262_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_262_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
v_a_280_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_260_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_260_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg___boxed(lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms(lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_293_, v_a_301_, v_a_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___boxed(lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms(v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec(v_a_305_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref_known(v___x_321_, 1);
v___x_322_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_323_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_322_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_332_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_332_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_preds_328_; lean_object* v___x_330_; 
v_preds_328_ = lean_ctor_get(v_a_324_, 3);
lean_inc(v_preds_328_);
lean_dec(v_a_324_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v_preds_328_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_preds_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
v_a_333_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_323_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_323_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_a_341_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_321_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_321_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg___boxed(lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds(lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_354_, v_a_362_, v_a_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___boxed(lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds(v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec(v_a_366_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec_ref_known(v___x_382_, 1);
v___x_383_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_384_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_383_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_393_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_393_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_sourceTypes_389_; lean_object* v___x_391_; 
v_sourceTypes_389_ = lean_ctor_get(v_a_385_, 4);
lean_inc(v_sourceTypes_389_);
lean_dec(v_a_385_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v_sourceTypes_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_sourceTypes_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
v_a_394_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_384_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_384_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_a_402_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_382_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_382_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg___boxed(lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes(lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_415_, v_a_423_, v_a_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___boxed(lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes(v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec(v_a_427_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(lean_object* v_e_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_440_, v_a_448_, v_a_449_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_487_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_487_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_487_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_487_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
if (lean_obj_tag(v_a_452_) == 0)
{
lean_object* v___x_456_; 
lean_del_object(v___x_454_);
lean_inc_ref(v_e_439_);
v___x_456_ = l_Lean_Meta_Sym_inferType(v_e_439_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_474_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_474_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_474_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_474_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Expr_getAppFn(v_a_457_);
lean_dec(v_a_457_);
if (lean_obj_tag(v___x_461_) == 4)
{
lean_object* v_declName_462_; uint8_t v___x_463_; 
v_declName_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_declName_462_);
lean_dec_ref_known(v___x_461_, 2);
v___x_463_ = l_Lean_NameSet_contains(v_a_452_, v_declName_462_);
lean_dec(v_declName_462_);
lean_dec_ref_known(v_a_452_, 5);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_466_; 
lean_dec_ref(v_e_439_);
v___x_464_ = lean_box(0);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_464_);
v___x_466_ = v___x_459_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_del_object(v___x_459_);
v___x_468_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_469_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_468_, v_e_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
return v___x_469_;
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_472_; 
lean_dec_ref(v___x_461_);
lean_dec_ref_known(v_a_452_, 5);
lean_dec_ref(v_e_439_);
v___x_470_ = lean_box(0);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_470_);
v___x_472_ = v___x_459_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref_known(v_a_452_, 5);
lean_dec_ref(v_e_439_);
v_a_475_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_456_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_456_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
else
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec_ref(v_e_439_);
v___x_483_ = lean_box(0);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_483_);
v___x_485_ = v___x_454_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_e_439_);
v_a_488_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_451_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_451_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm___boxed(lean_object* v_e_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(v_e_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec(v_a_497_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(lean_object* v_msgData_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; lean_object* v_env_516_; lean_object* v___x_517_; lean_object* v_toCold_518_; lean_object* v_mctx_519_; lean_object* v_lctx_520_; lean_object* v_options_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_515_ = lean_st_ref_get(v___y_513_);
v_env_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_ref(v_env_516_);
lean_dec(v___x_515_);
v___x_517_ = lean_st_ref_get(v___y_511_);
v_toCold_518_ = lean_ctor_get(v___y_512_, 0);
v_mctx_519_ = lean_ctor_get(v___x_517_, 0);
lean_inc_ref(v_mctx_519_);
lean_dec(v___x_517_);
v_lctx_520_ = lean_ctor_get(v___y_510_, 2);
v_options_521_ = lean_ctor_get(v_toCold_518_, 2);
lean_inc_ref(v_options_521_);
lean_inc_ref(v_lctx_520_);
v___x_522_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_522_, 0, v_env_516_);
lean_ctor_set(v___x_522_, 1, v_mctx_519_);
lean_ctor_set(v___x_522_, 2, v_lctx_520_);
lean_ctor_set(v___x_522_, 3, v_options_521_);
v___x_523_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v_msgData_509_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0___boxed(lean_object* v_msgData_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(v_msgData_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_531_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_532_; double v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_float_of_nat(v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(lean_object* v_cls_537_, lean_object* v_msg_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_ref_544_; lean_object* v___x_545_; lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_591_; 
v_ref_544_ = lean_ctor_get(v___y_541_, 2);
v___x_545_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(v_msg_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_591_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_591_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_591_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v_traceState_551_; lean_object* v_env_552_; lean_object* v_nextMacroScope_553_; lean_object* v_ngen_554_; lean_object* v_auxDeclNGen_555_; lean_object* v_cache_556_; lean_object* v_recordedDeps_557_; lean_object* v_messages_558_; lean_object* v_infoState_559_; lean_object* v_snapshotTasks_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_590_; 
v___x_550_ = lean_st_ref_take(v___y_542_);
v_traceState_551_ = lean_ctor_get(v___x_550_, 4);
v_env_552_ = lean_ctor_get(v___x_550_, 0);
v_nextMacroScope_553_ = lean_ctor_get(v___x_550_, 1);
v_ngen_554_ = lean_ctor_get(v___x_550_, 2);
v_auxDeclNGen_555_ = lean_ctor_get(v___x_550_, 3);
v_cache_556_ = lean_ctor_get(v___x_550_, 5);
v_recordedDeps_557_ = lean_ctor_get(v___x_550_, 6);
v_messages_558_ = lean_ctor_get(v___x_550_, 7);
v_infoState_559_ = lean_ctor_get(v___x_550_, 8);
v_snapshotTasks_560_ = lean_ctor_get(v___x_550_, 9);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_590_ == 0)
{
v___x_562_ = v___x_550_;
v_isShared_563_ = v_isSharedCheck_590_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_snapshotTasks_560_);
lean_inc(v_infoState_559_);
lean_inc(v_messages_558_);
lean_inc(v_recordedDeps_557_);
lean_inc(v_cache_556_);
lean_inc(v_traceState_551_);
lean_inc(v_auxDeclNGen_555_);
lean_inc(v_ngen_554_);
lean_inc(v_nextMacroScope_553_);
lean_inc(v_env_552_);
lean_dec(v___x_550_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_590_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
uint64_t v_tid_564_; lean_object* v_traces_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_589_; 
v_tid_564_ = lean_ctor_get_uint64(v_traceState_551_, sizeof(void*)*1);
v_traces_565_ = lean_ctor_get(v_traceState_551_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v_traceState_551_);
if (v_isSharedCheck_589_ == 0)
{
v___x_567_ = v_traceState_551_;
v_isShared_568_ = v_isSharedCheck_589_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_traces_565_);
lean_dec(v_traceState_551_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_589_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; double v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_569_ = lean_box(0);
v___x_570_ = lean_box(0);
v___x_571_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0);
v___x_572_ = 0;
v___x_573_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__1));
v___x_574_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_574_, 0, v_cls_537_);
lean_ctor_set(v___x_574_, 1, v___x_570_);
lean_ctor_set(v___x_574_, 2, v___x_573_);
lean_ctor_set_float(v___x_574_, sizeof(void*)*3, v___x_571_);
lean_ctor_set_float(v___x_574_, sizeof(void*)*3 + 8, v___x_571_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*3 + 16, v___x_572_);
v___x_575_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__2));
v___x_576_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set(v___x_576_, 1, v_a_546_);
lean_ctor_set(v___x_576_, 2, v___x_575_);
lean_inc(v_ref_544_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_ref_544_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = l_Lean_PersistentArray_push___redArg(v_traces_565_, v___x_577_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_578_);
v___x_580_ = v___x_567_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_578_);
lean_ctor_set_uint64(v_reuseFailAlloc_588_, sizeof(void*)*1, v_tid_564_);
v___x_580_ = v_reuseFailAlloc_588_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 4, v___x_580_);
v___x_582_ = v___x_562_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_env_552_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_nextMacroScope_553_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_ngen_554_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v_auxDeclNGen_555_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_587_, 5, v_cache_556_);
lean_ctor_set(v_reuseFailAlloc_587_, 6, v_recordedDeps_557_);
lean_ctor_set(v_reuseFailAlloc_587_, 7, v_messages_558_);
lean_ctor_set(v_reuseFailAlloc_587_, 8, v_infoState_559_);
lean_ctor_set(v_reuseFailAlloc_587_, 9, v_snapshotTasks_560_);
v___x_582_ = v_reuseFailAlloc_587_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = lean_st_ref_put(v___y_542_, v___x_582_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_569_);
v___x_585_ = v___x_548_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_569_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___boxed(lean_object* v_cls_592_, lean_object* v_msg_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v_cls_592_, v_msg_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_599_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_));
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1));
v___x_605_ = l_Lean_Name_append(v___x_604_, v___x_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(lean_object* v_generation_606_, lean_object* v_as_607_, size_t v_sz_608_, size_t v_i_609_, lean_object* v_b_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_lt(v_i_609_, v_sz_608_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec(v_generation_606_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v_b_610_);
return v___x_623_;
}
else
{
lean_object* v_a_624_; lean_object* v_toCold_625_; lean_object* v_options_626_; lean_object* v_fst_627_; lean_object* v_snd_628_; lean_object* v_inheritedTraceOptions_629_; uint8_t v_hasTrace_630_; lean_object* v___x_631_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; 
v_a_624_ = lean_array_uget_borrowed(v_as_607_, v_i_609_);
v_toCold_625_ = lean_ctor_get(v___y_619_, 0);
v_options_626_ = lean_ctor_get(v_toCold_625_, 2);
v_fst_627_ = lean_ctor_get(v_a_624_, 0);
v_snd_628_ = lean_ctor_get(v_a_624_, 1);
v_inheritedTraceOptions_629_ = lean_ctor_get(v_toCold_625_, 11);
v_hasTrace_630_ = lean_ctor_get_uint8(v_options_626_, sizeof(void*)*1);
v___x_631_ = lean_box(0);
if (v_hasTrace_630_ == 0)
{
v___y_633_ = v___y_611_;
v___y_634_ = v___y_612_;
v___y_635_ = v___y_613_;
v___y_636_ = v___y_614_;
v___y_637_ = v___y_615_;
v___y_638_ = v___y_616_;
v___y_639_ = v___y_617_;
v___y_640_ = v___y_618_;
v___y_641_ = v___y_619_;
v___y_642_ = v___y_620_;
goto v___jp_632_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_));
v___x_650_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2);
v___x_651_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_629_, v_options_626_, v___x_650_);
if (v___x_651_ == 0)
{
v___y_633_ = v___y_611_;
v___y_634_ = v___y_612_;
v___y_635_ = v___y_613_;
v___y_636_ = v___y_614_;
v___y_637_ = v___y_615_;
v___y_638_ = v___y_616_;
v___y_639_ = v___y_617_;
v___y_640_ = v___y_618_;
v___y_641_ = v___y_619_;
v___y_642_ = v___y_620_;
goto v___jp_632_;
}
else
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Meta_Grind_updateLastTag(v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec_ref_known(v___x_652_, 1);
lean_inc(v_snd_628_);
v___x_653_ = l_Lean_MessageData_ofExpr(v_snd_628_);
v___x_654_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_649_, v___x_653_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_dec_ref_known(v___x_654_, 1);
v___y_633_ = v___y_611_;
v___y_634_ = v___y_612_;
v___y_635_ = v___y_613_;
v___y_636_ = v___y_614_;
v___y_637_ = v___y_615_;
v___y_638_ = v___y_616_;
v___y_639_ = v___y_617_;
v___y_640_ = v___y_618_;
v___y_641_ = v___y_619_;
v___y_642_ = v___y_620_;
goto v___jp_632_;
}
else
{
lean_dec(v_generation_606_);
return v___x_654_;
}
}
else
{
lean_dec(v_generation_606_);
return v___x_652_;
}
}
}
v___jp_632_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_box(6);
v___x_644_ = lean_box(1);
lean_inc(v_generation_606_);
lean_inc(v_snd_628_);
lean_inc(v_fst_627_);
v___x_645_ = l_Lean_Meta_Grind_addNewRawFact(v_fst_627_, v_snd_628_, v_generation_606_, v___x_643_, v___x_644_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_645_) == 0)
{
size_t v___x_646_; size_t v___x_647_; 
lean_dec_ref_known(v___x_645_, 1);
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_add(v_i_609_, v___x_646_);
v_i_609_ = v___x_647_;
v_b_610_ = v___x_631_;
goto _start;
}
else
{
lean_dec(v_generation_606_);
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___boxed(lean_object* v_generation_655_, lean_object* v_as_656_, lean_object* v_sz_657_, lean_object* v_i_658_, lean_object* v_b_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
size_t v_sz_boxed_671_; size_t v_i_boxed_672_; lean_object* v_res_673_; 
v_sz_boxed_671_ = lean_unbox_usize(v_sz_657_);
lean_dec(v_sz_657_);
v_i_boxed_672_ = lean_unbox_usize(v_i_658_);
lean_dec(v_i_658_);
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(v_generation_655_, v_as_656_, v_sz_boxed_671_, v_i_boxed_672_, v_b_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v_as_656_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(lean_object* v_e_674_, lean_object* v_generation_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Expr_getAppFn(v_e_674_);
if (lean_obj_tag(v___x_687_) == 4)
{
lean_object* v_declName_688_; lean_object* v___x_689_; 
v_declName_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_declName_688_);
lean_dec_ref_known(v___x_687_, 2);
v___x_689_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_676_, v_a_684_, v_a_685_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_721_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_721_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_721_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_721_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
uint8_t v___x_694_; 
v___x_694_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_688_, v_a_690_);
lean_dec(v_a_690_);
lean_dec(v_declName_688_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_697_; 
lean_dec(v_generation_675_);
lean_dec_ref(v_e_674_);
v___x_695_ = lean_box(0);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_695_);
v___x_697_ = v___x_692_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
else
{
lean_object* v___x_699_; 
lean_del_object(v___x_692_);
v___x_699_ = l_Lean_Meta_Grind_mkHomoPredInstances(v_e_674_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; size_t v_sz_702_; size_t v___x_703_; lean_object* v___x_704_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = lean_box(0);
v_sz_702_ = lean_array_size(v_a_700_);
v___x_703_ = ((size_t)0ULL);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(v_generation_675_, v_a_700_, v_sz_702_, v___x_703_, v___x_701_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
lean_dec(v_a_700_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v___x_704_, 0);
lean_dec(v_unused_712_);
v___x_706_ = v___x_704_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_dec(v___x_704_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_701_);
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_701_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
return v___x_704_;
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_generation_675_);
v_a_713_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_699_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_699_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_declName_688_);
lean_dec(v_generation_675_);
lean_dec_ref(v_e_674_);
v_a_722_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_689_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_689_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref(v___x_687_);
lean_dec(v_generation_675_);
lean_dec_ref(v_e_674_);
v___x_730_ = lean_box(0);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds___boxed(lean_object* v_e_732_, lean_object* v_generation_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(v_e_732_, v_generation_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec(v_a_734_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0(lean_object* v_cls_746_, lean_object* v_msg_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v_cls_746_, v_msg_747_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___boxed(lean_object* v_cls_760_, lean_object* v_msg_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0(v_cls_760_, v_msg_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec(v___y_762_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f(lean_object* v_c_774_){
_start:
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_nat_dec_eq(v_c_774_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = lean_nat_sub(v_c_774_, v___x_777_);
v___x_779_ = lean_nat_lxor(v_c_774_, v___x_778_);
lean_dec(v___x_778_);
v___x_780_ = lean_nat_log2(v___x_779_);
lean_dec(v___x_779_);
v___x_781_ = lean_nat_shiftr(v_c_774_, v___x_780_);
v___x_782_ = lean_nat_log2(v___x_781_);
v___x_783_ = lean_nat_add(v___x_782_, v___x_777_);
lean_dec(v___x_782_);
v___x_784_ = lean_nat_add(v___x_781_, v___x_777_);
lean_dec(v___x_781_);
v___x_785_ = lean_nat_shiftl(v___x_777_, v___x_783_);
v___x_786_ = lean_nat_dec_eq(v___x_784_, v___x_785_);
lean_dec(v___x_785_);
lean_dec(v___x_784_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
lean_dec(v___x_783_);
lean_dec(v___x_780_);
v___x_787_ = lean_box(0);
return v___x_787_;
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_783_);
lean_ctor_set(v___x_788_, 1, v___x_780_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
else
{
lean_object* v___x_790_; 
v___x_790_ = lean_box(0);
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f___boxed(lean_object* v_c_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f(v_c_791_);
lean_dec(v_c_791_);
return v_res_792_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = l_Lean_Level_ofNat(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = lean_box(0);
v___x_801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3);
v___x_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v___x_800_);
return v___x_802_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4);
v___x_804_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3);
v___x_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_803_);
return v___x_805_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5);
v___x_807_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3);
v___x_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
return v___x_808_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6);
v___x_810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2));
v___x_811_ = l_Lean_mkConst(v___x_810_, v___x_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv(lean_object* v_a_812_, lean_object* v_b_813_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_814_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7);
v___x_815_ = l_Lean_Nat_mkType;
v___x_816_ = l_Lean_Nat_mkInstHDiv;
v___x_817_ = l_Lean_mkApp6(v___x_814_, v___x_815_, v___x_815_, v___x_815_, v___x_816_, v_a_812_, v_b_813_);
return v___x_817_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6);
v___x_824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2));
v___x_825_ = l_Lean_mkConst(v___x_824_, v___x_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod(lean_object* v_a_826_, lean_object* v_b_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3);
v___x_829_ = l_Lean_Nat_mkType;
v___x_830_ = l_Lean_Nat_mkInstHMod;
v___x_831_ = l_Lean_mkApp6(v___x_828_, v___x_829_, v___x_829_, v___x_829_, v___x_830_, v_a_826_, v_b_827_);
return v___x_831_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = l_Lean_Level_ofNat(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_box(0);
v___x_840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3);
v___x_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v___x_839_);
return v___x_841_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4);
v___x_843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2));
v___x_844_ = l_Lean_mkConst(v___x_843_, v___x_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(lean_object* v_a_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5);
v___x_847_ = l_Lean_Nat_mkType;
v___x_848_ = l_Lean_mkAppB(v___x_846_, v___x_847_, v_a_845_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg(lean_object* v_e_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; uint8_t v___y_899_; lean_object* v___y_900_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = l_Lean_Expr_cleanupAnnotations(v_e_883_);
v___x_928_ = l_Lean_Expr_isApp(v___x_927_);
if (v___x_928_ == 0)
{
lean_dec_ref(v___x_927_);
goto v___jp_924_;
}
else
{
lean_object* v_arg_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_arg_929_ = lean_ctor_get(v___x_927_, 1);
lean_inc_ref(v_arg_929_);
v___x_930_ = l_Lean_Expr_appFnCleanup___redArg(v___x_927_);
v___x_931_ = l_Lean_Expr_isApp(v___x_930_);
if (v___x_931_ == 0)
{
lean_dec_ref(v___x_930_);
lean_dec_ref(v_arg_929_);
goto v___jp_924_;
}
else
{
lean_object* v_arg_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v_arg_932_ = lean_ctor_get(v___x_930_, 1);
lean_inc_ref(v_arg_932_);
v___x_933_ = l_Lean_Expr_appFnCleanup___redArg(v___x_930_);
v___x_934_ = l_Lean_Expr_isApp(v___x_933_);
if (v___x_934_ == 0)
{
lean_dec_ref(v___x_933_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
goto v___jp_924_;
}
else
{
lean_object* v_arg_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_arg_935_ = lean_ctor_get(v___x_933_, 1);
lean_inc_ref(v_arg_935_);
v___x_936_ = l_Lean_Expr_appFnCleanup___redArg(v___x_933_);
v___x_937_ = l_Lean_Expr_isApp(v___x_936_);
if (v___x_937_ == 0)
{
lean_dec_ref(v___x_936_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
goto v___jp_924_;
}
else
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = l_Lean_Expr_appFnCleanup___redArg(v___x_936_);
v___x_939_ = l_Lean_Expr_isApp(v___x_938_);
if (v___x_939_ == 0)
{
lean_dec_ref(v___x_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
goto v___jp_924_;
}
else
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = l_Lean_Expr_appFnCleanup___redArg(v___x_938_);
v___x_941_ = l_Lean_Expr_isApp(v___x_940_);
if (v___x_941_ == 0)
{
lean_dec_ref(v___x_940_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
goto v___jp_924_;
}
else
{
lean_object* v_arg_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_arg_942_ = lean_ctor_get(v___x_940_, 1);
lean_inc_ref(v_arg_942_);
v___x_943_ = l_Lean_Expr_appFnCleanup___redArg(v___x_940_);
v___x_944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3));
v___x_945_ = l_Lean_Expr_isConstOf(v___x_943_, v___x_944_);
lean_dec_ref(v___x_943_);
if (v___x_945_ == 0)
{
lean_dec_ref(v_arg_942_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
goto v___jp_924_;
}
else
{
lean_object* v_fst_947_; lean_object* v_fst_948_; lean_object* v_fst_949_; uint8_t v_snd_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__13));
v___x_1003_ = l_Lean_Expr_isConstOf(v_arg_942_, v___x_1002_);
lean_dec_ref(v_arg_942_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
v___x_1004_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1004_, 0, v___x_1003_);
lean_ctor_set_uint8(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Meta_Structural_isInstHAndNat___redArg(v_arg_935_, v_a_887_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1027_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1027_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1027_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
uint8_t v___x_1011_; 
v___x_1011_ = lean_unbox(v_a_1007_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; uint8_t v___x_1013_; uint8_t v___x_1014_; lean_object* v___x_1016_; 
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
v___x_1012_ = lean_alloc_ctor(0, 0, 2);
v___x_1013_ = lean_unbox(v_a_1007_);
lean_ctor_set_uint8(v___x_1012_, 0, v___x_1013_);
v___x_1014_ = lean_unbox(v_a_1007_);
lean_dec(v_a_1007_);
lean_ctor_set_uint8(v___x_1012_, 1, v___x_1014_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1012_);
v___x_1016_ = v___x_1009_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1012_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
else
{
lean_object* v___x_1018_; 
lean_dec(v_a_1007_);
lean_inc_ref(v_arg_929_);
v___x_1018_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_929_);
if (lean_obj_tag(v___x_1018_) == 1)
{
lean_object* v_val_1019_; uint8_t v___x_1020_; 
lean_del_object(v___x_1009_);
v_val_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_val_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = 0;
v_fst_947_ = v_arg_932_;
v_fst_948_ = v_arg_929_;
v_fst_949_ = v_val_1019_;
v_snd_950_ = v___x_1020_;
v___y_951_ = v_a_884_;
v___y_952_ = v_a_885_;
v___y_953_ = v_a_886_;
v___y_954_ = v_a_887_;
v___y_955_ = v_a_888_;
v___y_956_ = v_a_889_;
goto v___jp_946_;
}
else
{
lean_object* v___x_1021_; 
lean_dec(v___x_1018_);
lean_inc_ref(v_arg_932_);
v___x_1021_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_932_);
if (lean_obj_tag(v___x_1021_) == 1)
{
lean_object* v_val_1022_; 
lean_del_object(v___x_1009_);
v_val_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_val_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v_fst_947_ = v_arg_929_;
v_fst_948_ = v_arg_932_;
v_fst_949_ = v_val_1022_;
v_snd_950_ = v___x_945_;
v___y_951_ = v_a_884_;
v___y_952_ = v_a_885_;
v___y_953_ = v_a_886_;
v___y_954_ = v_a_887_;
v___y_955_ = v_a_888_;
v___y_956_ = v_a_889_;
goto v___jp_946_;
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_dec(v___x_1021_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
v___x_1023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0));
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1023_);
v___x_1025_ = v___x_1009_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
v_a_1028_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1006_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1006_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
v___jp_946_:
{
lean_object* v___x_957_; 
v___x_957_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f(v_fst_949_);
lean_dec(v_fst_949_);
if (lean_obj_tag(v___x_957_) == 1)
{
lean_object* v_val_958_; lean_object* v_fst_959_; lean_object* v_snd_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v_val_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v___x_957_, 1);
v_fst_959_ = lean_ctor_get(v_val_958_, 0);
lean_inc_n(v_fst_959_, 2);
v_snd_960_ = lean_ctor_get(v_val_958_, 1);
lean_inc(v_snd_960_);
lean_dec(v_val_958_);
v___x_961_ = l_Lean_mkNatLit(v_fst_959_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_shiftl(v___x_962_, v_fst_959_);
lean_dec(v_fst_959_);
v___x_964_ = l_Lean_mkNatLit(v___x_963_);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = lean_nat_dec_eq(v_snd_960_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_inc(v_snd_960_);
v___x_967_ = l_Lean_mkNatLit(v_snd_960_);
v___x_968_ = lean_nat_shiftl(v___x_962_, v_snd_960_);
lean_dec(v_snd_960_);
v___x_969_ = l_Lean_mkNatLit(v___x_968_);
lean_inc_ref_n(v___x_969_, 2);
lean_inc_ref(v_fst_947_);
v___x_970_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv(v_fst_947_, v___x_969_);
lean_inc_ref(v___x_964_);
v___x_971_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod(v___x_970_, v___x_964_);
v___x_972_ = l_Lean_mkNatMul(v___x_971_, v___x_969_);
v___x_973_ = l_Lean_Meta_Sym_shareCommonInc(v___x_972_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
if (lean_obj_tag(v___x_973_) == 0)
{
if (v_snd_950_ == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6));
v___y_892_ = v___x_964_;
v___y_893_ = v_a_974_;
v___y_894_ = v___x_969_;
v___y_895_ = v___x_961_;
v___y_896_ = v_fst_947_;
v___y_897_ = v___x_967_;
v___y_898_ = v_fst_948_;
v___y_899_ = v___x_966_;
v___y_900_ = v___x_975_;
goto v___jp_891_;
}
else
{
lean_object* v_a_976_; lean_object* v___x_977_; 
v_a_976_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_973_, 1);
v___x_977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8));
v___y_892_ = v___x_964_;
v___y_893_ = v_a_976_;
v___y_894_ = v___x_969_;
v___y_895_ = v___x_961_;
v___y_896_ = v_fst_947_;
v___y_897_ = v___x_967_;
v___y_898_ = v_fst_948_;
v___y_899_ = v___x_966_;
v___y_900_ = v___x_977_;
goto v___jp_891_;
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref(v___x_969_);
lean_dec_ref(v___x_967_);
lean_dec_ref(v___x_964_);
lean_dec_ref(v___x_961_);
lean_dec_ref(v_fst_948_);
lean_dec_ref(v_fst_947_);
v_a_978_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_973_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_973_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec(v_snd_960_);
lean_inc_ref(v___x_964_);
lean_inc_ref(v_fst_947_);
v___x_986_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod(v_fst_947_, v___x_964_);
v___x_987_ = l_Lean_Meta_Sym_shareCommonInc(v___x_986_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
if (lean_obj_tag(v___x_987_) == 0)
{
if (v_snd_950_ == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10));
v___y_910_ = v_a_988_;
v___y_911_ = v___x_964_;
v___y_912_ = v___x_961_;
v___y_913_ = v_fst_947_;
v___y_914_ = v_fst_948_;
v___y_915_ = v___x_989_;
goto v___jp_909_;
}
else
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_987_, 1);
v___x_991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12));
v___y_910_ = v_a_990_;
v___y_911_ = v___x_964_;
v___y_912_ = v___x_961_;
v___y_913_ = v_fst_947_;
v___y_914_ = v_fst_948_;
v___y_915_ = v___x_991_;
goto v___jp_909_;
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec_ref(v___x_964_);
lean_dec_ref(v___x_961_);
lean_dec_ref(v_fst_948_);
lean_dec_ref(v_fst_947_);
v_a_992_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_987_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_987_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec(v___x_957_);
lean_dec_ref(v_fst_948_);
lean_dec_ref(v_fst_947_);
v___x_1000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0));
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
}
}
}
}
}
}
}
v___jp_891_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_901_ = lean_box(0);
lean_inc(v___y_900_);
v___x_902_ = l_Lean_mkConst(v___y_900_, v___x_901_);
lean_inc_ref(v___y_898_);
v___x_903_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(v___y_898_);
lean_inc_ref(v___y_894_);
v___x_904_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(v___y_894_);
lean_inc_ref(v___y_892_);
v___x_905_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(v___y_892_);
v___x_906_ = l_Lean_mkApp9(v___x_902_, v___y_896_, v___y_898_, v___y_894_, v___y_892_, v___y_897_, v___y_895_, v___x_903_, v___x_904_, v___x_905_);
v___x_907_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_907_, 0, v___y_893_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
lean_ctor_set_uint8(v___x_907_, sizeof(void*)*2, v___y_899_);
lean_ctor_set_uint8(v___x_907_, sizeof(void*)*2 + 1, v___y_899_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
v___jp_909_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_916_ = lean_box(0);
lean_inc(v___y_915_);
v___x_917_ = l_Lean_mkConst(v___y_915_, v___x_916_);
lean_inc_ref(v___y_914_);
v___x_918_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(v___y_914_);
lean_inc_ref(v___y_911_);
v___x_919_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(v___y_911_);
v___x_920_ = l_Lean_mkApp6(v___x_917_, v___y_913_, v___y_914_, v___y_911_, v___y_912_, v___x_918_, v___x_919_);
v___x_921_ = 0;
v___x_922_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_922_, 0, v___y_910_);
lean_ctor_set(v___x_922_, 1, v___x_920_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*2, v___x_921_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*2 + 1, v___x_921_);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
v___jp_924_:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0));
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___boxed(lean_object* v_e_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg(v_e_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc(lean_object* v_e_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg(v_e_1045_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___boxed(lean_object* v_e_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc(v_e_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
return v_res_1068_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1069_, lean_object* v_i_1070_, lean_object* v_k_1071_){
_start:
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = lean_array_get_size(v_keys_1069_);
v___x_1073_ = lean_nat_dec_lt(v_i_1070_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec(v_i_1070_);
return v___x_1073_;
}
else
{
lean_object* v_k_x27_1074_; size_t v___x_1075_; size_t v___x_1076_; uint8_t v___x_1077_; 
v_k_x27_1074_ = lean_array_fget_borrowed(v_keys_1069_, v_i_1070_);
v___x_1075_ = lean_ptr_addr(v_k_1071_);
v___x_1076_ = lean_ptr_addr(v_k_x27_1074_);
v___x_1077_ = lean_usize_dec_eq(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(1u);
v___x_1079_ = lean_nat_add(v_i_1070_, v___x_1078_);
lean_dec(v_i_1070_);
v_i_1070_ = v___x_1079_;
goto _start;
}
else
{
lean_dec(v_i_1070_);
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1081_, lean_object* v_i_1082_, lean_object* v_k_1083_){
_start:
{
uint8_t v_res_1084_; lean_object* v_r_1085_; 
v_res_1084_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_keys_1081_, v_i_1082_, v_k_1083_);
lean_dec_ref(v_k_1083_);
lean_dec_ref(v_keys_1081_);
v_r_1085_ = lean_box(v_res_1084_);
return v_r_1085_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(lean_object* v_x_1086_, size_t v_x_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
lean_object* v_es_1089_; lean_object* v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; lean_object* v_j_1093_; lean_object* v___x_1094_; 
v_es_1089_ = lean_ctor_get(v_x_1086_, 0);
v___x_1090_ = lean_box(2);
v___x_1091_ = ((size_t)31ULL);
v___x_1092_ = lean_usize_land(v_x_1087_, v___x_1091_);
v_j_1093_ = lean_usize_to_nat(v___x_1092_);
v___x_1094_ = lean_array_get_borrowed(v___x_1090_, v_es_1089_, v_j_1093_);
lean_dec(v_j_1093_);
switch(lean_obj_tag(v___x_1094_))
{
case 0:
{
lean_object* v_key_1095_; size_t v___x_1096_; size_t v___x_1097_; uint8_t v___x_1098_; 
v_key_1095_ = lean_ctor_get(v___x_1094_, 0);
v___x_1096_ = lean_ptr_addr(v_x_1088_);
v___x_1097_ = lean_ptr_addr(v_key_1095_);
v___x_1098_ = lean_usize_dec_eq(v___x_1096_, v___x_1097_);
return v___x_1098_;
}
case 1:
{
lean_object* v_node_1099_; size_t v___x_1100_; size_t v___x_1101_; 
v_node_1099_ = lean_ctor_get(v___x_1094_, 0);
v___x_1100_ = ((size_t)5ULL);
v___x_1101_ = lean_usize_shift_right(v_x_1087_, v___x_1100_);
v_x_1086_ = v_node_1099_;
v_x_1087_ = v___x_1101_;
goto _start;
}
default: 
{
uint8_t v___x_1103_; 
v___x_1103_ = 0;
return v___x_1103_;
}
}
}
else
{
lean_object* v_ks_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v_ks_1104_ = lean_ctor_get(v_x_1086_, 0);
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_ks_1104_, v___x_1105_, v_x_1088_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg___boxed(lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
size_t v_x_8976__boxed_1110_; uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_x_8976__boxed_1110_ = lean_unbox_usize(v_x_1108_);
lean_dec(v_x_1108_);
v_res_1111_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_1107_, v_x_8976__boxed_1110_, v_x_1109_);
lean_dec_ref(v_x_1109_);
lean_dec_ref(v_x_1107_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
size_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; uint64_t v___x_1118_; size_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1115_ = lean_ptr_addr(v_x_1114_);
v___x_1116_ = ((size_t)3ULL);
v___x_1117_ = lean_usize_shift_right(v___x_1115_, v___x_1116_);
v___x_1118_ = lean_usize_to_uint64(v___x_1117_);
v___x_1119_ = lean_uint64_to_usize(v___x_1118_);
v___x_1120_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_1113_, v___x_1119_, v_x_1114_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg___boxed(lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_x_1121_, v_x_1122_);
lean_dec_ref(v_x_1122_);
lean_dec_ref(v_x_1121_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(lean_object* v_val_1126_, uint8_t v___x_1127_, lean_object* v___x_1128_, lean_object* v_a_1129_, lean_object* v_e_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___y_1142_; lean_object* v_a_1143_; lean_object* v___y_1157_; lean_object* v___y_1160_; lean_object* v___y_1161_; uint8_t v___y_1162_; lean_object* v___x_1165_; 
lean_inc_ref(v_e_1130_);
v___x_1165_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v_e_1130_, v___x_1128_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
if (lean_obj_tag(v_a_1166_) == 0)
{
uint8_t v_done_1167_; uint8_t v_contextDependent_1168_; lean_object* v___y_1170_; lean_object* v_a_1171_; lean_object* v___y_1175_; 
v_done_1167_ = lean_ctor_get_uint8(v_a_1166_, 0);
v_contextDependent_1168_ = lean_ctor_get_uint8(v_a_1166_, 1);
if (v_done_1167_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref_known(v___x_1165_, 1);
v___x_1177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___closed__0));
lean_inc_ref(v_e_1130_);
v___x_1178_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_1129_, v___x_1177_, v_e_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
if (lean_obj_tag(v_a_1179_) == 0)
{
uint8_t v_done_1180_; 
v_done_1180_ = lean_ctor_get_uint8(v_a_1179_, 0);
if (v_done_1180_ == 0)
{
uint8_t v_contextDependent_1181_; lean_object* v___x_1182_; 
lean_inc_ref(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v_contextDependent_1181_ = lean_ctor_get_uint8(v_a_1179_, 1);
lean_dec_ref_known(v_a_1179_, 0);
lean_inc_ref(v_e_1130_);
v___x_1182_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg(v_e_1130_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; uint8_t v___y_1185_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
if (v_contextDependent_1181_ == 0)
{
v___y_1175_ = v___x_1182_;
goto v___jp_1174_;
}
else
{
if (lean_obj_tag(v_a_1183_) == 0)
{
uint8_t v_contextDependent_1195_; 
v_contextDependent_1195_ = lean_ctor_get_uint8(v_a_1183_, 1);
v___y_1185_ = v_contextDependent_1195_;
goto v___jp_1184_;
}
else
{
uint8_t v_contextDependent_1196_; 
v_contextDependent_1196_ = lean_ctor_get_uint8(v_a_1183_, sizeof(void*)*2 + 1);
v___y_1185_ = v_contextDependent_1196_;
goto v___jp_1184_;
}
}
v___jp_1184_:
{
if (v___y_1185_ == 0)
{
lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1193_; 
lean_inc(v_a_1183_);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v___x_1182_, 0);
lean_dec(v_unused_1194_);
v___x_1187_ = v___x_1182_;
v_isShared_1188_ = v_isSharedCheck_1193_;
goto v_resetjp_1186_;
}
else
{
lean_dec(v___x_1182_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1193_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1183_);
lean_inc_ref(v___x_1189_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1189_);
v___x_1191_ = v___x_1187_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v___y_1170_ = v___x_1191_;
v_a_1171_ = v___x_1189_;
goto v___jp_1169_;
}
}
}
else
{
v___y_1175_ = v___x_1182_;
goto v___jp_1174_;
}
}
}
else
{
v___y_1175_ = v___x_1182_;
goto v___jp_1174_;
}
}
else
{
v___y_1175_ = v___x_1178_;
goto v___jp_1174_;
}
}
else
{
v___y_1175_ = v___x_1178_;
goto v___jp_1174_;
}
}
else
{
v___y_1175_ = v___x_1178_;
goto v___jp_1174_;
}
}
else
{
v___y_1157_ = v___x_1165_;
goto v___jp_1156_;
}
v___jp_1169_:
{
if (v_contextDependent_1168_ == 0)
{
v___y_1142_ = v___y_1170_;
v_a_1143_ = v_a_1171_;
goto v___jp_1141_;
}
else
{
if (lean_obj_tag(v_a_1171_) == 0)
{
uint8_t v_contextDependent_1172_; 
v_contextDependent_1172_ = lean_ctor_get_uint8(v_a_1171_, 1);
v___y_1160_ = v___y_1170_;
v___y_1161_ = v_a_1171_;
v___y_1162_ = v_contextDependent_1172_;
goto v___jp_1159_;
}
else
{
uint8_t v_contextDependent_1173_; 
v_contextDependent_1173_ = lean_ctor_get_uint8(v_a_1171_, sizeof(void*)*2 + 1);
v___y_1160_ = v___y_1170_;
v___y_1161_ = v_a_1171_;
v___y_1162_ = v_contextDependent_1173_;
goto v___jp_1159_;
}
}
}
v___jp_1174_:
{
if (lean_obj_tag(v___y_1175_) == 0)
{
lean_object* v_a_1176_; 
v_a_1176_ = lean_ctor_get(v___y_1175_, 0);
lean_inc(v_a_1176_);
v___y_1170_ = v___y_1175_;
v_a_1171_ = v_a_1176_;
goto v___jp_1169_;
}
else
{
lean_dec_ref(v_e_1130_);
return v___y_1175_;
}
}
}
else
{
v___y_1157_ = v___x_1165_;
goto v___jp_1156_;
}
}
else
{
v___y_1157_ = v___x_1165_;
goto v___jp_1156_;
}
v___jp_1141_:
{
if (lean_obj_tag(v_a_1143_) == 0)
{
uint8_t v_done_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1155_; 
v_done_1144_ = lean_ctor_get_uint8(v_a_1143_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_a_1143_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1146_ = v_a_1143_;
v_isShared_1147_ = v_isSharedCheck_1155_;
goto v_resetjp_1145_;
}
else
{
lean_dec(v_a_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1155_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
if (v_done_1144_ == 0)
{
lean_object* v_toGoalState_1148_; lean_object* v_enodeMap_1149_; uint8_t v___x_1150_; lean_object* v___x_1152_; 
lean_dec_ref(v___y_1142_);
v_toGoalState_1148_ = lean_ctor_get(v_val_1126_, 0);
v_enodeMap_1149_ = lean_ctor_get(v_toGoalState_1148_, 1);
v___x_1150_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_enodeMap_1149_, v_e_1130_);
lean_dec_ref(v_e_1130_);
if (v_isShared_1147_ == 0)
{
v___x_1152_ = v___x_1146_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 0, 2);
v___x_1152_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; 
lean_ctor_set_uint8(v___x_1152_, 0, v___x_1150_);
lean_ctor_set_uint8(v___x_1152_, 1, v___x_1127_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
else
{
lean_del_object(v___x_1146_);
lean_dec_ref(v_e_1130_);
return v___y_1142_;
}
}
}
else
{
lean_dec_ref(v_a_1143_);
lean_dec_ref(v_e_1130_);
return v___y_1142_;
}
}
v___jp_1156_:
{
if (lean_obj_tag(v___y_1157_) == 0)
{
lean_object* v_a_1158_; 
v_a_1158_ = lean_ctor_get(v___y_1157_, 0);
lean_inc(v_a_1158_);
v___y_1142_ = v___y_1157_;
v_a_1143_ = v_a_1158_;
goto v___jp_1141_;
}
else
{
lean_dec_ref(v_e_1130_);
return v___y_1157_;
}
}
v___jp_1159_:
{
if (v___y_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec_ref(v___y_1160_);
v___x_1163_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1161_);
lean_inc_ref(v___x_1163_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
v___y_1142_ = v___x_1164_;
v_a_1143_ = v___x_1163_;
goto v___jp_1141_;
}
else
{
v___y_1142_ = v___y_1160_;
v_a_1143_ = v___y_1161_;
goto v___jp_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed(lean_object* v_val_1197_, lean_object* v___x_1198_, lean_object* v___x_1199_, lean_object* v_a_1200_, lean_object* v_e_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
uint8_t v___x_9041__boxed_1212_; lean_object* v_res_1213_; 
v___x_9041__boxed_1212_ = lean_unbox(v___x_1198_);
v_res_1213_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(v_val_1197_, v___x_9041__boxed_1212_, v___x_1199_, v_a_1200_, v_e_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v_a_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v_val_1197_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_st_ref_get(v_a_1217_);
v___x_1222_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1234_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___f_1230_; lean_object* v___x_1232_; 
v___x_1227_ = 0;
v___x_1228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0));
v___x_1229_ = lean_box(v___x_1227_);
v___f_1230_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed), 15, 4);
lean_closure_set(v___f_1230_, 0, v___x_1221_);
lean_closure_set(v___f_1230_, 1, v___x_1229_);
lean_closure_set(v___f_1230_, 2, v___x_1228_);
lean_closure_set(v___f_1230_, 3, v_a_1223_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___f_1230_);
v___x_1232_ = v___x_1225_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___f_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec(v___x_1221_);
v_a_1235_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1222_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1222_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___boxed(lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter(lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_1248_, v_a_1256_, v_a_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___boxed(lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter(v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec(v_a_1260_);
return v_res_1271_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0(lean_object* v_00_u03b2_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
uint8_t v___x_1275_; 
v___x_1275_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_x_1273_, v_x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___boxed(lean_object* v_00_u03b2_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_res_1279_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0(v_00_u03b2_1276_, v_x_1277_, v_x_1278_);
lean_dec_ref(v_x_1278_);
lean_dec_ref(v_x_1277_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0(lean_object* v_00_u03b2_1281_, lean_object* v_x_1282_, size_t v_x_1283_, lean_object* v_x_1284_){
_start:
{
uint8_t v___x_1285_; 
v___x_1285_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_1282_, v_x_1283_, v_x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
size_t v_x_9282__boxed_1290_; uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_x_9282__boxed_1290_ = lean_unbox_usize(v_x_1288_);
lean_dec(v_x_1288_);
v_res_1291_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0(v_00_u03b2_1286_, v_x_1287_, v_x_9282__boxed_1290_, v_x_1289_);
lean_dec_ref(v_x_1289_);
lean_dec_ref(v_x_1287_);
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1293_, lean_object* v_keys_1294_, lean_object* v_vals_1295_, lean_object* v_heq_1296_, lean_object* v_i_1297_, lean_object* v_k_1298_){
_start:
{
uint8_t v___x_1299_; 
v___x_1299_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_keys_1294_, v_i_1297_, v_k_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1300_, lean_object* v_keys_1301_, lean_object* v_vals_1302_, lean_object* v_heq_1303_, lean_object* v_i_1304_, lean_object* v_k_1305_){
_start:
{
uint8_t v_res_1306_; lean_object* v_r_1307_; 
v_res_1306_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1(v_00_u03b2_1300_, v_keys_1301_, v_vals_1302_, v_heq_1303_, v_i_1304_, v_k_1305_);
lean_dec_ref(v_k_1305_);
lean_dec_ref(v_vals_1302_);
lean_dec_ref(v_keys_1301_);
v_r_1307_ = lean_box(v_res_1306_);
return v_r_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__0(lean_object* v_s_1308_){
_start:
{
lean_object* v_internalized_1309_; uint8_t v_initialized_1310_; lean_object* v_thms_1311_; lean_object* v_preds_1312_; lean_object* v_sourceTypes_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1321_; 
v_internalized_1309_ = lean_ctor_get(v_s_1308_, 1);
v_initialized_1310_ = lean_ctor_get_uint8(v_s_1308_, sizeof(void*)*5);
v_thms_1311_ = lean_ctor_get(v_s_1308_, 2);
v_preds_1312_ = lean_ctor_get(v_s_1308_, 3);
v_sourceTypes_1313_ = lean_ctor_get(v_s_1308_, 4);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_s_1308_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v_s_1308_, 0);
lean_dec(v_unused_1322_);
v___x_1315_ = v_s_1308_;
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_sourceTypes_1313_);
lean_inc(v_preds_1312_);
lean_inc(v_thms_1311_);
lean_inc(v_internalized_1309_);
lean_dec(v_s_1308_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1317_);
v___x_1319_ = v___x_1315_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_internalized_1309_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_thms_1311_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v_preds_1312_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v_sourceTypes_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*5, v_initialized_1310_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1(lean_object* v_snd_1323_, lean_object* v_s_1324_){
_start:
{
lean_object* v_persistentCache_1325_; lean_object* v_internalized_1326_; uint8_t v_initialized_1327_; lean_object* v_thms_1328_; lean_object* v_preds_1329_; lean_object* v_sourceTypes_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_persistentCache_1325_ = lean_ctor_get(v_snd_1323_, 1);
v_internalized_1326_ = lean_ctor_get(v_s_1324_, 1);
v_initialized_1327_ = lean_ctor_get_uint8(v_s_1324_, sizeof(void*)*5);
v_thms_1328_ = lean_ctor_get(v_s_1324_, 2);
v_preds_1329_ = lean_ctor_get(v_s_1324_, 3);
v_sourceTypes_1330_ = lean_ctor_get(v_s_1324_, 4);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_s_1324_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v_s_1324_, 0);
lean_dec(v_unused_1338_);
v___x_1332_ = v_s_1324_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_sourceTypes_1330_);
lean_inc(v_preds_1329_);
lean_inc(v_thms_1328_);
lean_inc(v_internalized_1326_);
lean_dec(v_s_1324_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
lean_inc_ref(v_persistentCache_1325_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v_persistentCache_1325_);
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_persistentCache_1325_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_internalized_1326_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_thms_1328_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v_preds_1329_);
lean_ctor_set(v_reuseFailAlloc_1336_, 4, v_sourceTypes_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1336_, sizeof(void*)*5, v_initialized_1327_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1___boxed(lean_object* v_snd_1339_, lean_object* v_s_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1(v_snd_1339_, v_s_1340_);
lean_dec_ref(v_snd_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(lean_object* v_e_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___f_1355_; lean_object* v___x_1356_; 
v___f_1355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__0));
v___x_1356_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_1347_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc_n(v_a_1357_, 2);
lean_dec_ref_known(v___x_1356_, 1);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v_a_1357_);
lean_ctor_set(v___x_1358_, 1, v_a_1357_);
v___x_1359_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_1360_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_1359_, v_a_1347_, v_a_1352_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v_cache_1362_; lean_object* v___x_1363_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v_cache_1362_ = lean_ctor_get(v_a_1361_, 0);
lean_inc_ref(v_cache_1362_);
lean_dec(v_a_1361_);
v___x_1363_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1359_, v___f_1355_, v_a_1347_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec_ref_known(v___x_1363_, 1);
v___x_1364_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1364_, 0, v_e_1346_);
v___x_1365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__1));
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_1368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v_cache_1362_);
lean_ctor_set(v___x_1368_, 2, v___x_1367_);
lean_ctor_set(v___x_1368_, 3, v___x_1367_);
v___x_1369_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_1364_, v___x_1358_, v___x_1365_, v___x_1368_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v_fst_1371_; lean_object* v_snd_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1404_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v_fst_1371_ = lean_ctor_get(v_a_1370_, 0);
v_snd_1372_ = lean_ctor_get(v_a_1370_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_a_1370_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1374_ = v_a_1370_;
v_isShared_1375_ = v_isSharedCheck_1404_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snd_1372_);
lean_inc(v_fst_1371_);
lean_dec(v_a_1370_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1404_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___f_1376_; lean_object* v___x_1377_; 
v___f_1376_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1376_, 0, v_snd_1372_);
v___x_1377_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1359_, v___f_1376_, v_a_1347_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1394_; 
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; 
v_unused_1395_ = lean_ctor_get(v___x_1377_, 0);
lean_dec(v_unused_1395_);
v___x_1379_ = v___x_1377_;
v_isShared_1380_ = v_isSharedCheck_1394_;
goto v_resetjp_1378_;
}
else
{
lean_dec(v___x_1377_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1394_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
if (lean_obj_tag(v_fst_1371_) == 1)
{
lean_object* v_e_x27_1381_; lean_object* v_proof_1382_; lean_object* v___x_1384_; 
v_e_x27_1381_ = lean_ctor_get(v_fst_1371_, 0);
lean_inc_ref(v_e_x27_1381_);
v_proof_1382_ = lean_ctor_get(v_fst_1371_, 1);
lean_inc_ref(v_proof_1382_);
lean_dec_ref_known(v_fst_1371_, 2);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v_proof_1382_);
lean_ctor_set(v___x_1374_, 0, v_e_x27_1381_);
v___x_1384_ = v___x_1374_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_e_x27_1381_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_proof_1382_);
v___x_1384_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1385_);
v___x_1387_ = v___x_1379_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_del_object(v___x_1374_);
lean_dec(v_fst_1371_);
v___x_1390_ = lean_box(0);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1390_);
v___x_1392_ = v___x_1379_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_del_object(v___x_1374_);
lean_dec(v_fst_1371_);
v_a_1396_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1377_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1377_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1369_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1369_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_cache_1362_);
lean_dec_ref_known(v___x_1358_, 2);
lean_dec_ref(v_e_1346_);
v_a_1413_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1363_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1363_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec_ref_known(v___x_1358_, 2);
lean_dec_ref(v_e_1346_);
v_a_1421_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1360_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1360_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec_ref(v_e_1346_);
v_a_1429_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1356_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1356_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___boxed(lean_object* v_e_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f(lean_object* v_e_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1447_, v_a_1448_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___boxed(lean_object* v_e_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f(v_e_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec(v_a_1461_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_){
_start:
{
lean_object* v_ks_1477_; lean_object* v_vs_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1504_; 
v_ks_1477_ = lean_ctor_get(v_x_1473_, 0);
v_vs_1478_ = lean_ctor_get(v_x_1473_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_x_1473_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1480_ = v_x_1473_;
v_isShared_1481_ = v_isSharedCheck_1504_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_vs_1478_);
lean_inc(v_ks_1477_);
lean_dec(v_x_1473_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1504_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1482_ = lean_array_get_size(v_ks_1477_);
v___x_1483_ = lean_nat_dec_lt(v_x_1474_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
lean_dec(v_x_1474_);
v___x_1484_ = lean_array_push(v_ks_1477_, v_x_1475_);
v___x_1485_ = lean_array_push(v_vs_1478_, v_x_1476_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___x_1485_);
lean_ctor_set(v___x_1480_, 0, v___x_1484_);
v___x_1487_ = v___x_1480_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
else
{
lean_object* v_k_x27_1489_; size_t v___x_1490_; size_t v___x_1491_; uint8_t v___x_1492_; 
v_k_x27_1489_ = lean_array_fget_borrowed(v_ks_1477_, v_x_1474_);
v___x_1490_ = lean_ptr_addr(v_x_1475_);
v___x_1491_ = lean_ptr_addr(v_k_x27_1489_);
v___x_1492_ = lean_usize_dec_eq(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1494_; 
if (v_isShared_1481_ == 0)
{
v___x_1494_ = v___x_1480_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_ks_1477_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_vs_1478_);
v___x_1494_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1496_ = lean_nat_add(v_x_1474_, v___x_1495_);
lean_dec(v_x_1474_);
v_x_1473_ = v___x_1494_;
v_x_1474_ = v___x_1496_;
goto _start;
}
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1499_ = lean_array_fset(v_ks_1477_, v_x_1474_, v_x_1475_);
v___x_1500_ = lean_array_fset(v_vs_1478_, v_x_1474_, v_x_1476_);
lean_dec(v_x_1474_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___x_1500_);
lean_ctor_set(v___x_1480_, 0, v___x_1499_);
v___x_1502_ = v___x_1480_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1505_, lean_object* v_k_1506_, lean_object* v_v_1507_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1505_, v___x_1508_, v_k_1506_, v_v_1507_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(lean_object* v_x_1511_, size_t v_x_1512_, size_t v_x_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_){
_start:
{
if (lean_obj_tag(v_x_1511_) == 0)
{
lean_object* v_es_1516_; size_t v___x_1517_; size_t v___x_1518_; lean_object* v_j_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v_es_1516_ = lean_ctor_get(v_x_1511_, 0);
v___x_1517_ = ((size_t)31ULL);
v___x_1518_ = lean_usize_land(v_x_1512_, v___x_1517_);
v_j_1519_ = lean_usize_to_nat(v___x_1518_);
v___x_1520_ = lean_array_get_size(v_es_1516_);
v___x_1521_ = lean_nat_dec_lt(v_j_1519_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_dec(v_j_1519_);
lean_dec(v_x_1515_);
lean_dec_ref(v_x_1514_);
return v_x_1511_;
}
else
{
lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1562_; 
lean_inc_ref(v_es_1516_);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_x_1511_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v_x_1511_, 0);
lean_dec(v_unused_1563_);
v___x_1523_ = v_x_1511_;
v_isShared_1524_ = v_isSharedCheck_1562_;
goto v_resetjp_1522_;
}
else
{
lean_dec(v_x_1511_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1562_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_v_1525_; lean_object* v___x_1526_; lean_object* v_xs_x27_1527_; lean_object* v___y_1529_; 
v_v_1525_ = lean_array_fget(v_es_1516_, v_j_1519_);
v___x_1526_ = lean_box(0);
v_xs_x27_1527_ = lean_array_fset(v_es_1516_, v_j_1519_, v___x_1526_);
switch(lean_obj_tag(v_v_1525_))
{
case 0:
{
lean_object* v_key_1534_; lean_object* v_val_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1547_; 
v_key_1534_ = lean_ctor_get(v_v_1525_, 0);
v_val_1535_ = lean_ctor_get(v_v_1525_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_v_1525_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1537_ = v_v_1525_;
v_isShared_1538_ = v_isSharedCheck_1547_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_val_1535_);
lean_inc(v_key_1534_);
lean_dec(v_v_1525_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1547_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
size_t v___x_1539_; size_t v___x_1540_; uint8_t v___x_1541_; 
v___x_1539_ = lean_ptr_addr(v_x_1514_);
v___x_1540_ = lean_ptr_addr(v_key_1534_);
v___x_1541_ = lean_usize_dec_eq(v___x_1539_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_del_object(v___x_1537_);
v___x_1542_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1534_, v_val_1535_, v_x_1514_, v_x_1515_);
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
v___y_1529_ = v___x_1543_;
goto v___jp_1528_;
}
else
{
lean_object* v___x_1545_; 
lean_dec(v_val_1535_);
lean_dec(v_key_1534_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 1, v_x_1515_);
lean_ctor_set(v___x_1537_, 0, v_x_1514_);
v___x_1545_ = v___x_1537_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_x_1514_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_x_1515_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
v___y_1529_ = v___x_1545_;
goto v___jp_1528_;
}
}
}
}
case 1:
{
lean_object* v_node_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1560_; 
v_node_1548_ = lean_ctor_get(v_v_1525_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_v_1525_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1550_ = v_v_1525_;
v_isShared_1551_ = v_isSharedCheck_1560_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_node_1548_);
lean_dec(v_v_1525_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1560_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
size_t v___x_1552_; size_t v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1552_ = ((size_t)5ULL);
v___x_1553_ = lean_usize_shift_right(v_x_1512_, v___x_1552_);
v___x_1554_ = ((size_t)1ULL);
v___x_1555_ = lean_usize_add(v_x_1513_, v___x_1554_);
v___x_1556_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_node_1548_, v___x_1553_, v___x_1555_, v_x_1514_, v_x_1515_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1556_);
v___x_1558_ = v___x_1550_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
v___y_1529_ = v___x_1558_;
goto v___jp_1528_;
}
}
}
default: 
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_x_1514_);
lean_ctor_set(v___x_1561_, 1, v_x_1515_);
v___y_1529_ = v___x_1561_;
goto v___jp_1528_;
}
}
v___jp_1528_:
{
lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1530_ = lean_array_fset(v_xs_x27_1527_, v_j_1519_, v___y_1529_);
lean_dec(v_j_1519_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1530_);
v___x_1532_ = v___x_1523_;
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
}
}
else
{
lean_object* v_ks_1564_; lean_object* v_vs_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1583_; 
v_ks_1564_ = lean_ctor_get(v_x_1511_, 0);
v_vs_1565_ = lean_ctor_get(v_x_1511_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_x_1511_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1567_ = v_x_1511_;
v_isShared_1568_ = v_isSharedCheck_1583_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_vs_1565_);
lean_inc(v_ks_1564_);
lean_dec(v_x_1511_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1583_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_ks_1564_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_vs_1565_);
v___x_1570_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v_newNode_1571_; size_t v___x_1572_; uint8_t v___x_1573_; 
v_newNode_1571_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(v___x_1570_, v_x_1514_, v_x_1515_);
v___x_1572_ = ((size_t)7ULL);
v___x_1573_ = lean_usize_dec_le(v___x_1572_, v_x_1513_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1574_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1571_);
v___x_1575_ = lean_unsigned_to_nat(4u);
v___x_1576_ = lean_nat_dec_lt(v___x_1574_, v___x_1575_);
lean_dec(v___x_1574_);
if (v___x_1576_ == 0)
{
lean_object* v_ks_1577_; lean_object* v_vs_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_ks_1577_ = lean_ctor_get(v_newNode_1571_, 0);
lean_inc_ref(v_ks_1577_);
v_vs_1578_ = lean_ctor_get(v_newNode_1571_, 1);
lean_inc_ref(v_vs_1578_);
lean_dec_ref(v_newNode_1571_);
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0);
v___x_1581_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_x_1513_, v_ks_1577_, v_vs_1578_, v___x_1579_, v___x_1580_);
lean_dec_ref(v_vs_1578_);
lean_dec_ref(v_ks_1577_);
return v___x_1581_;
}
else
{
return v_newNode_1571_;
}
}
else
{
return v_newNode_1571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(size_t v_depth_1584_, lean_object* v_keys_1585_, lean_object* v_vals_1586_, lean_object* v_i_1587_, lean_object* v_entries_1588_){
_start:
{
lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = lean_array_get_size(v_keys_1585_);
v___x_1590_ = lean_nat_dec_lt(v_i_1587_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_dec(v_i_1587_);
return v_entries_1588_;
}
else
{
lean_object* v_k_1591_; lean_object* v_v_1592_; size_t v___x_1593_; size_t v___x_1594_; size_t v___x_1595_; uint64_t v___x_1596_; size_t v_h_1597_; size_t v___x_1598_; lean_object* v___x_1599_; size_t v___x_1600_; size_t v___x_1601_; size_t v___x_1602_; size_t v_h_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_k_1591_ = lean_array_fget_borrowed(v_keys_1585_, v_i_1587_);
v_v_1592_ = lean_array_fget_borrowed(v_vals_1586_, v_i_1587_);
v___x_1593_ = lean_ptr_addr(v_k_1591_);
v___x_1594_ = ((size_t)3ULL);
v___x_1595_ = lean_usize_shift_right(v___x_1593_, v___x_1594_);
v___x_1596_ = lean_usize_to_uint64(v___x_1595_);
v_h_1597_ = lean_uint64_to_usize(v___x_1596_);
v___x_1598_ = ((size_t)5ULL);
v___x_1599_ = lean_unsigned_to_nat(1u);
v___x_1600_ = ((size_t)1ULL);
v___x_1601_ = lean_usize_sub(v_depth_1584_, v___x_1600_);
v___x_1602_ = lean_usize_mul(v___x_1598_, v___x_1601_);
v_h_1603_ = lean_usize_shift_right(v_h_1597_, v___x_1602_);
v___x_1604_ = lean_nat_add(v_i_1587_, v___x_1599_);
lean_dec(v_i_1587_);
lean_inc(v_v_1592_);
lean_inc(v_k_1591_);
v___x_1605_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_entries_1588_, v_h_1603_, v_depth_1584_, v_k_1591_, v_v_1592_);
v_i_1587_ = v___x_1604_;
v_entries_1588_ = v___x_1605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1607_, lean_object* v_keys_1608_, lean_object* v_vals_1609_, lean_object* v_i_1610_, lean_object* v_entries_1611_){
_start:
{
size_t v_depth_boxed_1612_; lean_object* v_res_1613_; 
v_depth_boxed_1612_ = lean_unbox_usize(v_depth_1607_);
lean_dec(v_depth_1607_);
v_res_1613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1612_, v_keys_1608_, v_vals_1609_, v_i_1610_, v_entries_1611_);
lean_dec_ref(v_vals_1609_);
lean_dec_ref(v_keys_1608_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
size_t v_x_28805__boxed_1619_; size_t v_x_28806__boxed_1620_; lean_object* v_res_1621_; 
v_x_28805__boxed_1619_ = lean_unbox_usize(v_x_1615_);
lean_dec(v_x_1615_);
v_x_28806__boxed_1620_ = lean_unbox_usize(v_x_1616_);
lean_dec(v_x_1616_);
v_res_1621_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1614_, v_x_28805__boxed_1619_, v_x_28806__boxed_1620_, v_x_1617_, v_x_1618_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(lean_object* v_x_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_){
_start:
{
size_t v___x_1625_; size_t v___x_1626_; size_t v___x_1627_; uint64_t v___x_1628_; size_t v___x_1629_; size_t v___x_1630_; lean_object* v___x_1631_; 
v___x_1625_ = lean_ptr_addr(v_x_1623_);
v___x_1626_ = ((size_t)3ULL);
v___x_1627_ = lean_usize_shift_right(v___x_1625_, v___x_1626_);
v___x_1628_ = lean_usize_to_uint64(v___x_1627_);
v___x_1629_ = lean_uint64_to_usize(v___x_1628_);
v___x_1630_ = ((size_t)1ULL);
v___x_1631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1622_, v___x_1629_, v___x_1630_, v_x_1623_, v_x_1624_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___lam__0(lean_object* v_e_1632_, lean_object* v_s_1633_){
_start:
{
lean_object* v_cache_1634_; lean_object* v_internalized_1635_; uint8_t v_initialized_1636_; lean_object* v_thms_1637_; lean_object* v_preds_1638_; lean_object* v_sourceTypes_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1648_; 
v_cache_1634_ = lean_ctor_get(v_s_1633_, 0);
v_internalized_1635_ = lean_ctor_get(v_s_1633_, 1);
v_initialized_1636_ = lean_ctor_get_uint8(v_s_1633_, sizeof(void*)*5);
v_thms_1637_ = lean_ctor_get(v_s_1633_, 2);
v_preds_1638_ = lean_ctor_get(v_s_1633_, 3);
v_sourceTypes_1639_ = lean_ctor_get(v_s_1633_, 4);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_s_1633_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1641_ = v_s_1633_;
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_sourceTypes_1639_);
lean_inc(v_preds_1638_);
lean_inc(v_thms_1637_);
lean_inc(v_internalized_1635_);
lean_inc(v_cache_1634_);
lean_dec(v_s_1633_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1643_ = lean_box(0);
v___x_1644_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(v_internalized_1635_, v_e_1632_, v___x_1643_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 1, v___x_1644_);
v___x_1646_ = v___x_1641_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_cache_1634_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_thms_1637_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_preds_1638_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_sourceTypes_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1647_, sizeof(void*)*5, v_initialized_1636_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1652_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1));
v___x_1653_ = l_Lean_Name_append(v___x_1652_, v___x_1651_);
return v___x_1653_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2));
v___x_1656_ = l_Lean_stringToMessageData(v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg(lean_object* v_e_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v___f_1669_; lean_object* v___x_1670_; 
lean_inc_ref(v_e_1657_);
v___f_1669_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Homo_internalize___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1669_, 0, v_e_1657_);
v___x_1670_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1660_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1789_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1789_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1789_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
uint8_t v_hom_1675_; 
v_hom_1675_ = lean_ctor_get_uint8(v_a_1671_, sizeof(void*)*14 + 24);
lean_dec(v_a_1671_);
if (v_hom_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
lean_dec_ref(v___f_1669_);
lean_dec_ref(v_e_1657_);
v___x_1676_ = lean_box(0);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1676_);
v___x_1678_ = v___x_1673_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
else
{
lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0));
v___x_1681_ = l_Lean_Expr_isAppOf(v_e_1657_, v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_del_object(v___x_1673_);
v___x_1682_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_1683_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_1682_, v_a_1658_, v_a_1666_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1776_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1776_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1776_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v_internalized_1688_; uint8_t v___x_1689_; 
v_internalized_1688_ = lean_ctor_get(v_a_1684_, 1);
lean_inc_ref(v_internalized_1688_);
lean_dec(v_a_1684_);
v___x_1689_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_internalized_1688_, v_e_1657_);
lean_dec_ref(v_internalized_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; 
lean_del_object(v___x_1686_);
v___x_1690_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1682_, v___f_1669_, v_a_1658_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; 
lean_dec_ref_known(v___x_1690_, 1);
lean_inc_ref(v_e_1657_);
v___x_1691_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(v_e_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v___x_1692_; 
lean_dec_ref_known(v___x_1691_, 1);
v___x_1692_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1657_, v_a_1658_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
lean_inc_ref(v_e_1657_);
v___x_1694_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1657_, v_a_1658_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
if (lean_obj_tag(v_a_1695_) == 1)
{
lean_object* v_val_1696_; lean_object* v_fst_1697_; lean_object* v_snd_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1754_; 
v_val_1696_ = lean_ctor_get(v_a_1695_, 0);
lean_inc(v_val_1696_);
lean_dec_ref_known(v_a_1695_, 1);
v_fst_1697_ = lean_ctor_get(v_val_1696_, 0);
v_snd_1698_ = lean_ctor_get(v_val_1696_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_val_1696_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1700_ = v_val_1696_;
v_isShared_1701_ = v_isSharedCheck_1754_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snd_1698_);
lean_inc(v_fst_1697_);
lean_dec(v_val_1696_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1754_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; 
lean_inc(v_a_1667_);
lean_inc_ref(v_a_1666_);
lean_inc(v_a_1665_);
lean_inc_ref(v_a_1664_);
lean_inc(v_a_1663_);
lean_inc_ref(v_a_1662_);
lean_inc(v_a_1661_);
lean_inc_ref(v_a_1660_);
lean_inc(v_a_1659_);
lean_inc(v_a_1658_);
v___x_1702_ = lean_grind_preprocess(v_fst_1697_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1704_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc_n(v_a_1703_, 2);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = l_Lean_Meta_Simp_Result_getProof(v_a_1703_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1706_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1704_, 1);
v___x_1706_ = l_Lean_Meta_mkEqTrans(v_snd_1698_, v_a_1705_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v_expr_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v_expr_1708_ = lean_ctor_get(v_a_1703_, 0);
lean_inc_ref_n(v_expr_1708_, 2);
lean_dec(v_a_1703_);
v___x_1709_ = lean_box(0);
lean_inc(v_a_1667_);
lean_inc_ref(v_a_1666_);
lean_inc(v_a_1665_);
lean_inc_ref(v_a_1664_);
lean_inc(v_a_1663_);
lean_inc_ref(v_a_1662_);
lean_inc(v_a_1661_);
lean_inc_ref(v_a_1660_);
lean_inc(v_a_1659_);
lean_inc(v_a_1658_);
v___x_1710_ = lean_grind_internalize(v_expr_1708_, v_a_1693_, v___x_1709_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_toCold_1711_; lean_object* v_options_1712_; uint8_t v_hasTrace_1713_; 
lean_dec_ref_known(v___x_1710_, 1);
v_toCold_1711_ = lean_ctor_get(v_a_1666_, 0);
v_options_1712_ = lean_ctor_get(v_toCold_1711_, 2);
v_hasTrace_1713_ = lean_ctor_get_uint8(v_options_1712_, sizeof(void*)*1);
if (v_hasTrace_1713_ == 0)
{
lean_object* v___x_1714_; 
lean_del_object(v___x_1700_);
v___x_1714_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1657_, v_expr_1708_, v_a_1707_, v___x_1689_, v_a_1658_, v_a_1660_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
return v___x_1714_;
}
else
{
lean_object* v_inheritedTraceOptions_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v_inheritedTraceOptions_1715_ = lean_ctor_get(v_toCold_1711_, 11);
v___x_1716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1717_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1);
v___x_1718_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1715_, v_options_1712_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
lean_del_object(v___x_1700_);
v___x_1719_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1657_, v_expr_1708_, v_a_1707_, v___x_1689_, v_a_1658_, v_a_1660_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
return v___x_1719_;
}
else
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_Meta_Grind_updateLastTag(v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
lean_dec_ref_known(v___x_1720_, 1);
lean_inc_ref(v_e_1657_);
v___x_1721_ = l_Lean_MessageData_ofExpr(v_e_1657_);
v___x_1722_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3);
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 7);
lean_ctor_set(v___x_1700_, 1, v___x_1722_);
lean_ctor_set(v___x_1700_, 0, v___x_1721_);
v___x_1724_ = v___x_1700_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_inc_ref(v_expr_1708_);
v___x_1725_ = l_Lean_MessageData_ofExpr(v_expr_1708_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1724_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_1716_, v___x_1726_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v___x_1728_; 
lean_dec_ref_known(v___x_1727_, 1);
v___x_1728_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1657_, v_expr_1708_, v_a_1707_, v___x_1689_, v_a_1658_, v_a_1660_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
return v___x_1728_;
}
else
{
lean_dec_ref(v_expr_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_e_1657_);
return v___x_1727_;
}
}
}
else
{
lean_dec_ref(v_expr_1708_);
lean_dec(v_a_1707_);
lean_del_object(v___x_1700_);
lean_dec_ref(v_e_1657_);
return v___x_1720_;
}
}
}
}
else
{
lean_dec_ref(v_expr_1708_);
lean_dec(v_a_1707_);
lean_del_object(v___x_1700_);
lean_dec_ref(v_e_1657_);
return v___x_1710_;
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_a_1703_);
lean_del_object(v___x_1700_);
lean_dec(v_a_1693_);
lean_dec_ref(v_e_1657_);
v_a_1730_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1706_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1706_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec(v_a_1703_);
lean_del_object(v___x_1700_);
lean_dec(v_snd_1698_);
lean_dec(v_a_1693_);
lean_dec_ref(v_e_1657_);
v_a_1738_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1704_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1704_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_del_object(v___x_1700_);
lean_dec(v_snd_1698_);
lean_dec(v_a_1693_);
lean_dec_ref(v_e_1657_);
v_a_1746_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1702_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1702_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
else
{
lean_object* v___x_1755_; 
lean_dec(v_a_1695_);
v___x_1755_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(v_e_1657_, v_a_1693_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
return v___x_1755_;
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_a_1693_);
lean_dec_ref(v_e_1657_);
v_a_1756_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1694_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1694_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v_e_1657_);
v_a_1764_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1692_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1692_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_dec_ref(v_e_1657_);
return v___x_1691_;
}
}
else
{
lean_dec_ref(v_e_1657_);
return v___x_1690_;
}
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
lean_dec_ref(v___f_1669_);
lean_dec_ref(v_e_1657_);
v___x_1772_ = lean_box(0);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1772_);
v___x_1774_ = v___x_1686_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec_ref(v___f_1669_);
lean_dec_ref(v_e_1657_);
v_a_1777_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1683_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1683_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_dec_ref(v___f_1669_);
lean_dec_ref(v_e_1657_);
v___x_1785_ = lean_box(0);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1785_);
v___x_1787_ = v___x_1673_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v___f_1669_);
lean_dec_ref(v_e_1657_);
v_a_1790_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1670_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1670_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___boxed(lean_object* v_e_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_Meta_Grind_Homo_internalize___redArg(v_e_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec(v_a_1799_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize(lean_object* v_e_1811_, lean_object* v___parent_x3f_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_Meta_Grind_Homo_internalize___redArg(v_e_1811_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___boxed(lean_object* v_e_1825_, lean_object* v___parent_x3f_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Meta_Grind_Homo_internalize(v_e_1825_, v___parent_x3f_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec(v___parent_x3f_1826_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0(lean_object* v_00_u03b2_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(v_x_1840_, v_x_1841_, v_x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0(lean_object* v_00_u03b2_1844_, lean_object* v_x_1845_, size_t v_x_1846_, size_t v_x_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1845_, v_x_1846_, v_x_1847_, v_x_1848_, v_x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
size_t v_x_29304__boxed_1857_; size_t v_x_29305__boxed_1858_; lean_object* v_res_1859_; 
v_x_29304__boxed_1857_ = lean_unbox_usize(v_x_1853_);
lean_dec(v_x_1853_);
v_x_29305__boxed_1858_ = lean_unbox_usize(v_x_1854_);
lean_dec(v_x_1854_);
v_res_1859_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0(v_00_u03b2_1851_, v_x_1852_, v_x_29304__boxed_1857_, v_x_29305__boxed_1858_, v_x_1855_, v_x_1856_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1860_, lean_object* v_n_1861_, lean_object* v_k_1862_, lean_object* v_v_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(v_n_1861_, v_k_1862_, v_v_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1865_, size_t v_depth_1866_, lean_object* v_keys_1867_, lean_object* v_vals_1868_, lean_object* v_heq_1869_, lean_object* v_i_1870_, lean_object* v_entries_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_depth_1866_, v_keys_1867_, v_vals_1868_, v_i_1870_, v_entries_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1873_, lean_object* v_depth_1874_, lean_object* v_keys_1875_, lean_object* v_vals_1876_, lean_object* v_heq_1877_, lean_object* v_i_1878_, lean_object* v_entries_1879_){
_start:
{
size_t v_depth_boxed_1880_; lean_object* v_res_1881_; 
v_depth_boxed_1880_ = lean_unbox_usize(v_depth_1874_);
lean_dec(v_depth_1874_);
v_res_1881_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2(v_00_u03b2_1873_, v_depth_boxed_1880_, v_keys_1875_, v_vals_1876_, v_heq_1877_, v_i_1878_, v_entries_1879_);
lean_dec_ref(v_vals_1876_);
lean_dec_ref(v_keys_1875_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1883_, v_x_1884_, v_x_1885_, v_x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewEq(lean_object* v_a_1888_, lean_object* v_b_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1892_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_2049_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_2049_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_2049_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
uint8_t v_hom_1906_; 
v_hom_1906_ = lean_ctor_get_uint8(v_a_1902_, sizeof(void*)*14 + 24);
lean_dec(v_a_1902_);
if (v_hom_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
lean_dec_ref(v_b_1889_);
lean_dec_ref(v_a_1888_);
v___x_1907_ = lean_box(0);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1907_);
v___x_1909_ = v___x_1904_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
else
{
lean_object* v___x_1911_; 
lean_del_object(v___x_1904_);
lean_inc_ref(v_b_1889_);
lean_inc_ref(v_a_1888_);
v___x_1911_ = l_Lean_Meta_Grind_hasSameType(v_a_1888_, v_b_1889_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_2040_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_2040_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_2040_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_unbox(v_a_1912_);
lean_dec(v_a_1912_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; lean_object* v___x_1919_; 
lean_dec_ref(v_b_1889_);
lean_dec_ref(v_a_1888_);
v___x_1917_ = lean_box(0);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1917_);
v___x_1919_ = v___x_1914_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
else
{
lean_object* v___x_1921_; 
lean_del_object(v___x_1914_);
lean_inc_ref(v_b_1889_);
lean_inc_ref(v_a_1888_);
v___x_1921_ = l_Lean_Meta_mkEq(v_a_1888_, v_b_1889_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = l_Lean_Meta_Sym_shareCommon(v_a_1922_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc_n(v_a_1924_, 2);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_a_1924_, v_a_1890_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_2015_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_2015_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_2015_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
if (lean_obj_tag(v_a_1926_) == 1)
{
lean_object* v_val_1930_; lean_object* v_fst_1931_; lean_object* v_snd_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_2010_; 
lean_del_object(v___x_1928_);
v_val_1930_ = lean_ctor_get(v_a_1926_, 0);
lean_inc(v_val_1930_);
lean_dec_ref_known(v_a_1926_, 1);
v_fst_1931_ = lean_ctor_get(v_val_1930_, 0);
v_snd_1932_ = lean_ctor_get(v_val_1930_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_val_1930_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1934_ = v_val_1930_;
v_isShared_1935_ = v_isSharedCheck_2010_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_snd_1932_);
lean_inc(v_fst_1931_);
lean_dec(v_val_1930_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_2010_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; 
lean_inc(v_a_1899_);
lean_inc_ref(v_a_1898_);
lean_inc(v_a_1897_);
lean_inc_ref(v_a_1896_);
lean_inc(v_a_1895_);
lean_inc_ref(v_a_1894_);
lean_inc(v_a_1893_);
lean_inc_ref(v_a_1892_);
lean_inc(v_a_1891_);
lean_inc(v_a_1890_);
lean_inc_ref(v_b_1889_);
lean_inc_ref(v_a_1888_);
v___x_1936_ = lean_grind_mk_eq_proof(v_a_1888_, v_b_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = l_Lean_Meta_mkEqMP(v_snd_1932_, v_a_1937_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___x_1955_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1955_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1888_, v_a_1890_);
lean_dec_ref(v_a_1888_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1957_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1889_, v_a_1890_);
lean_dec_ref(v_b_1889_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___y_1960_; uint8_t v___x_1977_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1977_ = lean_nat_dec_le(v_a_1956_, v_a_1958_);
if (v___x_1977_ == 0)
{
lean_dec(v_a_1958_);
v___y_1960_ = v_a_1956_;
goto v___jp_1959_;
}
else
{
lean_dec(v_a_1956_);
v___y_1960_ = v_a_1958_;
goto v___jp_1959_;
}
v___jp_1959_:
{
lean_object* v_toCold_1961_; lean_object* v_options_1962_; uint8_t v_hasTrace_1963_; 
v_toCold_1961_ = lean_ctor_get(v_a_1898_, 0);
v_options_1962_ = lean_ctor_get(v_toCold_1961_, 2);
v_hasTrace_1963_ = lean_ctor_get_uint8(v_options_1962_, sizeof(void*)*1);
if (v_hasTrace_1963_ == 0)
{
lean_del_object(v___x_1934_);
lean_dec(v_a_1924_);
v___y_1941_ = v___y_1960_;
v___y_1942_ = v_a_1890_;
v___y_1943_ = v_a_1891_;
v___y_1944_ = v_a_1892_;
v___y_1945_ = v_a_1893_;
v___y_1946_ = v_a_1894_;
v___y_1947_ = v_a_1895_;
v___y_1948_ = v_a_1896_;
v___y_1949_ = v_a_1897_;
v___y_1950_ = v_a_1898_;
v___y_1951_ = v_a_1899_;
goto v___jp_1940_;
}
else
{
lean_object* v_inheritedTraceOptions_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v_inheritedTraceOptions_1964_ = lean_ctor_get(v_toCold_1961_, 11);
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1966_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1);
v___x_1967_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1964_, v_options_1962_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_del_object(v___x_1934_);
lean_dec(v_a_1924_);
v___y_1941_ = v___y_1960_;
v___y_1942_ = v_a_1890_;
v___y_1943_ = v_a_1891_;
v___y_1944_ = v_a_1892_;
v___y_1945_ = v_a_1893_;
v___y_1946_ = v_a_1894_;
v___y_1947_ = v_a_1895_;
v___y_1948_ = v_a_1896_;
v___y_1949_ = v_a_1897_;
v___y_1950_ = v_a_1898_;
v___y_1951_ = v_a_1899_;
goto v___jp_1940_;
}
else
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Meta_Grind_updateLastTag(v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
lean_dec_ref_known(v___x_1968_, 1);
v___x_1969_ = l_Lean_MessageData_ofExpr(v_a_1924_);
v___x_1970_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3);
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 7);
lean_ctor_set(v___x_1934_, 1, v___x_1970_);
lean_ctor_set(v___x_1934_, 0, v___x_1969_);
v___x_1972_ = v___x_1934_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_inc(v_fst_1931_);
v___x_1973_ = l_Lean_MessageData_ofExpr(v_fst_1931_);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_1965_, v___x_1974_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_dec_ref_known(v___x_1975_, 1);
v___y_1941_ = v___y_1960_;
v___y_1942_ = v_a_1890_;
v___y_1943_ = v_a_1891_;
v___y_1944_ = v_a_1892_;
v___y_1945_ = v_a_1893_;
v___y_1946_ = v_a_1894_;
v___y_1947_ = v_a_1895_;
v___y_1948_ = v_a_1896_;
v___y_1949_ = v_a_1897_;
v___y_1950_ = v_a_1898_;
v___y_1951_ = v_a_1899_;
goto v___jp_1940_;
}
else
{
lean_dec(v___y_1960_);
lean_dec(v_a_1939_);
lean_dec(v_fst_1931_);
return v___x_1975_;
}
}
}
else
{
lean_dec(v___y_1960_);
lean_dec(v_a_1939_);
lean_del_object(v___x_1934_);
lean_dec(v_fst_1931_);
lean_dec(v_a_1924_);
return v___x_1968_;
}
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v_a_1956_);
lean_dec(v_a_1939_);
lean_del_object(v___x_1934_);
lean_dec(v_fst_1931_);
lean_dec(v_a_1924_);
v_a_1978_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1957_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1957_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec(v_a_1939_);
lean_del_object(v___x_1934_);
lean_dec(v_fst_1931_);
lean_dec(v_a_1924_);
lean_dec_ref(v_b_1889_);
v_a_1986_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1955_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1955_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
v___jp_1940_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = lean_box(6);
v___x_1953_ = lean_box(1);
v___x_1954_ = l_Lean_Meta_Grind_addNewRawFact(v_a_1939_, v_fst_1931_, v___y_1941_, v___x_1952_, v___x_1953_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1954_;
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_del_object(v___x_1934_);
lean_dec(v_fst_1931_);
lean_dec(v_a_1924_);
lean_dec_ref(v_b_1889_);
lean_dec_ref(v_a_1888_);
v_a_1994_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1938_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1938_);
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
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_del_object(v___x_1934_);
lean_dec(v_snd_1932_);
lean_dec(v_fst_1931_);
lean_dec(v_a_1924_);
lean_dec_ref(v_b_1889_);
lean_dec_ref(v_a_1888_);
v_a_2002_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1936_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1936_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
lean_dec(v_a_1926_);
lean_dec(v_a_1924_);
lean_dec_ref(v_b_1889_);
lean_dec_ref(v_a_1888_);
v___x_2011_ = lean_box(0);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_2011_);
v___x_2013_ = v___x_1928_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_a_1924_);
lean_dec_ref(v_b_1889_);
lean_dec_ref(v_a_1888_);
v_a_2016_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1925_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1925_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_b_1889_);
lean_dec_ref(v_a_1888_);
v_a_2024_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1923_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_1923_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec_ref(v_b_1889_);
lean_dec_ref(v_a_1888_);
v_a_2032_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1921_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1921_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_b_1889_);
lean_dec_ref(v_a_1888_);
v_a_2041_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_1911_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_1911_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v_b_1889_);
lean_dec_ref(v_a_1888_);
v_a_2050_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_1901_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_1901_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewEq___boxed(lean_object* v_a_2058_, lean_object* v_b_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Meta_Grind_Homo_processNewEq(v_a_2058_, v_b_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec(v_a_2061_);
lean_dec(v_a_2060_);
return v_res_2071_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_box(0);
v___x_2076_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_processNewDiseq___closed__1));
v___x_2077_ = l_Lean_mkConst(v___x_2076_, v___x_2075_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq(lean_object* v_a_2078_, lean_object* v_b_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2082_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2253_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2253_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2253_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
uint8_t v_hom_2096_; 
v_hom_2096_ = lean_ctor_get_uint8(v_a_2092_, sizeof(void*)*14 + 24);
lean_dec(v_a_2092_);
if (v_hom_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
lean_dec_ref(v_b_2079_);
lean_dec_ref(v_a_2078_);
v___x_2097_ = lean_box(0);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2097_);
v___x_2099_ = v___x_2094_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
else
{
lean_object* v___x_2101_; 
lean_del_object(v___x_2094_);
lean_inc_ref(v_b_2079_);
lean_inc_ref(v_a_2078_);
v___x_2101_ = l_Lean_Meta_Grind_hasSameType(v_a_2078_, v_b_2079_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2244_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2244_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2244_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
uint8_t v___x_2106_; 
v___x_2106_ = lean_unbox(v_a_2102_);
lean_dec(v_a_2102_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_dec_ref(v_b_2079_);
lean_dec_ref(v_a_2078_);
v___x_2107_ = lean_box(0);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2107_);
v___x_2109_ = v___x_2104_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
else
{
lean_object* v___x_2111_; 
lean_del_object(v___x_2104_);
lean_inc_ref(v_b_2079_);
lean_inc_ref(v_a_2078_);
v___x_2111_ = l_Lean_Meta_mkEq(v_a_2078_, v_b_2079_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = l_Lean_Meta_Sym_shareCommon(v_a_2112_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc_n(v_a_2114_, 2);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_a_2114_, v_a_2080_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2219_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2219_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2219_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
if (lean_obj_tag(v_a_2116_) == 1)
{
lean_object* v_val_2120_; lean_object* v_fst_2121_; lean_object* v_snd_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2214_; 
lean_del_object(v___x_2118_);
v_val_2120_ = lean_ctor_get(v_a_2116_, 0);
lean_inc(v_val_2120_);
lean_dec_ref_known(v_a_2116_, 1);
v_fst_2121_ = lean_ctor_get(v_val_2120_, 0);
v_snd_2122_ = lean_ctor_get(v_val_2120_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_val_2120_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2124_ = v_val_2120_;
v_isShared_2125_ = v_isSharedCheck_2214_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_snd_2122_);
lean_inc(v_fst_2121_);
lean_dec(v_val_2120_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2214_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; 
lean_inc_ref(v_b_2079_);
lean_inc_ref(v_a_2078_);
v___x_2126_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_2078_, v_b_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2, &l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2_once, _init_l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2);
v___x_2129_ = l_Lean_Meta_mkCongrArg(v___x_2128_, v_snd_2122_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = l_Lean_Meta_mkEqMP(v_a_2130_, v_a_2127_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___x_2149_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2149_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_2078_, v_a_2080_);
lean_dec_ref(v_a_2078_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_2079_, v_a_2080_);
lean_dec_ref(v_b_2079_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___y_2154_; uint8_t v___x_2173_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
v___x_2173_ = lean_nat_dec_le(v_a_2150_, v_a_2152_);
if (v___x_2173_ == 0)
{
lean_dec(v_a_2152_);
v___y_2154_ = v_a_2150_;
goto v___jp_2153_;
}
else
{
lean_dec(v_a_2150_);
v___y_2154_ = v_a_2152_;
goto v___jp_2153_;
}
v___jp_2153_:
{
lean_object* v_toCold_2155_; lean_object* v_options_2156_; uint8_t v_hasTrace_2157_; 
v_toCold_2155_ = lean_ctor_get(v_a_2088_, 0);
v_options_2156_ = lean_ctor_get(v_toCold_2155_, 2);
v_hasTrace_2157_ = lean_ctor_get_uint8(v_options_2156_, sizeof(void*)*1);
if (v_hasTrace_2157_ == 0)
{
lean_del_object(v___x_2124_);
lean_dec(v_a_2114_);
v___y_2134_ = v___y_2154_;
v___y_2135_ = v_a_2080_;
v___y_2136_ = v_a_2081_;
v___y_2137_ = v_a_2082_;
v___y_2138_ = v_a_2083_;
v___y_2139_ = v_a_2084_;
v___y_2140_ = v_a_2085_;
v___y_2141_ = v_a_2086_;
v___y_2142_ = v_a_2087_;
v___y_2143_ = v_a_2088_;
v___y_2144_ = v_a_2089_;
goto v___jp_2133_;
}
else
{
lean_object* v_inheritedTraceOptions_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v_inheritedTraceOptions_2158_ = lean_ctor_get(v_toCold_2155_, 11);
v___x_2159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_2160_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1);
v___x_2161_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2158_, v_options_2156_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_del_object(v___x_2124_);
lean_dec(v_a_2114_);
v___y_2134_ = v___y_2154_;
v___y_2135_ = v_a_2080_;
v___y_2136_ = v_a_2081_;
v___y_2137_ = v_a_2082_;
v___y_2138_ = v_a_2083_;
v___y_2139_ = v_a_2084_;
v___y_2140_ = v_a_2085_;
v___y_2141_ = v_a_2086_;
v___y_2142_ = v_a_2087_;
v___y_2143_ = v_a_2088_;
v___y_2144_ = v_a_2089_;
goto v___jp_2133_;
}
else
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_Meta_Grind_updateLastTag(v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_dec_ref_known(v___x_2162_, 1);
v___x_2163_ = l_Lean_mkNot(v_a_2114_);
v___x_2164_ = l_Lean_MessageData_ofExpr(v___x_2163_);
v___x_2165_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3);
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 7);
lean_ctor_set(v___x_2124_, 1, v___x_2165_);
lean_ctor_set(v___x_2124_, 0, v___x_2164_);
v___x_2167_ = v___x_2124_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_inc(v_fst_2121_);
v___x_2168_ = l_Lean_mkNot(v_fst_2121_);
v___x_2169_ = l_Lean_MessageData_ofExpr(v___x_2168_);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2167_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_2159_, v___x_2170_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_dec_ref_known(v___x_2171_, 1);
v___y_2134_ = v___y_2154_;
v___y_2135_ = v_a_2080_;
v___y_2136_ = v_a_2081_;
v___y_2137_ = v_a_2082_;
v___y_2138_ = v_a_2083_;
v___y_2139_ = v_a_2084_;
v___y_2140_ = v_a_2085_;
v___y_2141_ = v_a_2086_;
v___y_2142_ = v_a_2087_;
v___y_2143_ = v_a_2088_;
v___y_2144_ = v_a_2089_;
goto v___jp_2133_;
}
else
{
lean_dec(v___y_2154_);
lean_dec(v_a_2132_);
lean_dec(v_fst_2121_);
return v___x_2171_;
}
}
}
else
{
lean_dec(v___y_2154_);
lean_dec(v_a_2132_);
lean_del_object(v___x_2124_);
lean_dec(v_fst_2121_);
lean_dec(v_a_2114_);
return v___x_2162_;
}
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_a_2150_);
lean_dec(v_a_2132_);
lean_del_object(v___x_2124_);
lean_dec(v_fst_2121_);
lean_dec(v_a_2114_);
v_a_2174_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2151_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2151_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_a_2132_);
lean_del_object(v___x_2124_);
lean_dec(v_fst_2121_);
lean_dec(v_a_2114_);
lean_dec_ref(v_b_2079_);
v_a_2182_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2149_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2149_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
v___jp_2133_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2145_ = l_Lean_mkNot(v_fst_2121_);
v___x_2146_ = lean_box(6);
v___x_2147_ = lean_box(1);
v___x_2148_ = l_Lean_Meta_Grind_addNewRawFact(v_a_2132_, v___x_2145_, v___y_2134_, v___x_2146_, v___x_2147_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
return v___x_2148_;
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_del_object(v___x_2124_);
lean_dec(v_fst_2121_);
lean_dec(v_a_2114_);
lean_dec_ref(v_b_2079_);
lean_dec_ref(v_a_2078_);
v_a_2190_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2131_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2131_);
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
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_a_2127_);
lean_del_object(v___x_2124_);
lean_dec(v_fst_2121_);
lean_dec(v_a_2114_);
lean_dec_ref(v_b_2079_);
lean_dec_ref(v_a_2078_);
v_a_2198_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2129_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2129_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_del_object(v___x_2124_);
lean_dec(v_snd_2122_);
lean_dec(v_fst_2121_);
lean_dec(v_a_2114_);
lean_dec_ref(v_b_2079_);
lean_dec_ref(v_a_2078_);
v_a_2206_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2126_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2126_);
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
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_dec(v_a_2116_);
lean_dec(v_a_2114_);
lean_dec_ref(v_b_2079_);
lean_dec_ref(v_a_2078_);
v___x_2215_ = lean_box(0);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2215_);
v___x_2217_ = v___x_2118_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_a_2114_);
lean_dec_ref(v_b_2079_);
lean_dec_ref(v_a_2078_);
v_a_2220_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2115_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2115_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec_ref(v_b_2079_);
lean_dec_ref(v_a_2078_);
v_a_2228_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2113_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2113_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref(v_b_2079_);
lean_dec_ref(v_a_2078_);
v_a_2236_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2111_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2111_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec_ref(v_b_2079_);
lean_dec_ref(v_a_2078_);
v_a_2245_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2101_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2101_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec_ref(v_b_2079_);
lean_dec_ref(v_a_2078_);
v_a_2254_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2091_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2091_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___boxed(lean_object* v_a_2262_, lean_object* v_b_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Meta_Grind_Homo_processNewDiseq(v_a_2262_, v_b_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec(v_a_2264_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_apply_11(v___y_2277_, v___y_2276_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, lean_box(0));
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec_ref(v___y_2292_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(uint8_t v___x_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = lean_box(v___x_2304_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___x_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
uint8_t v___x_1028__boxed_2330_; lean_object* v_res_2331_; 
v___x_1028__boxed_2330_ = lean_unbox(v___x_2318_);
v_res_2331_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___x_1028__boxed_2330_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec(v___y_2319_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object* v___x_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2332_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___x_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___x_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec(v___y_2346_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; lean_object* v___x_2375_; 
v___f_2368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2369_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___f_2373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___f_2374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2375_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2372_, v___f_2373_, v___f_2368_, v___f_2373_, v___f_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_();
return v_res_2377_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_Extra(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homomorphism(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_Homo_homExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_Homo_homExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Homomorphism(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_Extra(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Homomorphism(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homomorphism(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Homomorphism(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Homomorphism(builtin);
}
#ifdef __cplusplus
}
#endif
