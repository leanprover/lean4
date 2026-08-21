// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Homomorphism
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.Homo public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Tactic.Grind.Diseq import Lean.Meta.Sym.Simp.Rewrite
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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerSolverExtension___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\n===>\n"};
static const lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4;
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
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_114_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(lean_object* v___x_119_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object* v___x_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(v___x_122_);
return v_res_124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_125_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0(lean_box(0));
return v___x_128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_129_ = l_Lean_NameSet_empty;
v___x_130_ = lean_box(1);
v___x_131_ = 0;
v___x_132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_134_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
lean_ctor_set(v___x_134_, 2, v___x_133_);
lean_ctor_set(v___x_134_, 3, v___x_130_);
lean_ctor_set(v___x_134_, 4, v___x_129_);
lean_ctor_set_uint8(v___x_134_, sizeof(void*)*5, v___x_131_);
return v___x_134_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_135_; lean_object* v___f_136_; 
v___x_135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___f_136_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_136_, 0, v___x_135_);
return v___f_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_138_; lean_object* v___x_139_; 
v___f_138_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_139_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_();
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0(uint8_t v___x_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_s_146_){
_start:
{
lean_object* v_cache_147_; lean_object* v_internalized_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_cache_147_ = lean_ctor_get(v_s_146_, 0);
v_internalized_148_ = lean_ctor_get(v_s_146_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_s_146_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; lean_object* v_unused_157_; lean_object* v_unused_158_; 
v_unused_156_ = lean_ctor_get(v_s_146_, 4);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_s_146_, 3);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_s_146_, 2);
lean_dec(v_unused_158_);
v___x_150_ = v_s_146_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_internalized_148_);
lean_inc(v_cache_147_);
lean_dec(v_s_146_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 4, v_a_145_);
lean_ctor_set(v___x_150_, 3, v_a_144_);
lean_ctor_set(v___x_150_, 2, v_a_143_);
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_cache_147_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_internalized_148_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_a_143_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v_a_144_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v_a_145_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*5, v___x_142_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0___boxed(lean_object* v___x_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_s_163_){
_start:
{
uint8_t v___x_4124__boxed_164_; lean_object* v_res_165_; 
v___x_4124__boxed_164_ = lean_unbox(v___x_159_);
v_res_165_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0(v___x_4124__boxed_164_, v_a_160_, v_a_161_, v_a_162_, v_s_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_171_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_170_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_215_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_215_ == 0)
{
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_215_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_215_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
uint8_t v_initialized_176_; 
v_initialized_176_ = lean_ctor_get_uint8(v_a_172_, sizeof(void*)*5);
lean_dec(v_a_172_);
if (v_initialized_176_ == 0)
{
lean_object* v___x_177_; 
lean_del_object(v___x_174_);
v___x_177_ = l_Lean_Meta_Grind_getHomoTheorems___redArg(v_a_168_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_179_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v___x_179_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_168_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_168_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___f_185_; lean_object* v___x_186_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
v___x_183_ = 1;
v___x_184_ = lean_box(v___x_183_);
v___f_185_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_185_, 0, v___x_184_);
lean_closure_set(v___f_185_, 1, v_a_178_);
lean_closure_set(v___f_185_, 2, v_a_180_);
lean_closure_set(v___f_185_, 3, v_a_182_);
v___x_186_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_170_, v___f_185_, v_a_166_);
return v___x_186_;
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
lean_dec(v_a_180_);
lean_dec(v_a_178_);
v_a_187_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_181_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_181_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec(v_a_178_);
v_a_195_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_179_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_179_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_177_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_177_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
else
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_box(0);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_211_);
v___x_213_ = v___x_174_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
v_a_216_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_171_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_171_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___boxed(lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init(lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_229_, v_a_237_, v_a_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___boxed(lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init(v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec(v_a_241_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_253_, v_a_254_, v_a_255_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref_known(v___x_257_, 1);
v___x_258_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_259_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_258_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_268_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_268_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_thms_264_; lean_object* v___x_266_; 
v_thms_264_ = lean_ctor_get(v_a_260_, 2);
lean_inc_ref(v_thms_264_);
lean_dec(v_a_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v_thms_264_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_thms_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_259_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_259_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
v_a_277_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_257_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_257_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg___boxed(lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_285_, v_a_286_, v_a_287_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms(lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_290_, v_a_298_, v_a_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___boxed(lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms(v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec(v_a_302_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_314_, v_a_315_, v_a_316_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref_known(v___x_318_, 1);
v___x_319_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_320_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_319_, v_a_314_, v_a_315_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_329_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_329_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_preds_325_; lean_object* v___x_327_; 
v_preds_325_ = lean_ctor_get(v_a_321_, 3);
lean_inc(v_preds_325_);
lean_dec(v_a_321_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_preds_325_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_preds_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_a_330_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_320_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_320_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
v_a_338_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_318_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_318_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg___boxed(lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds(lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_351_, v_a_359_, v_a_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___boxed(lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds(v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec(v_a_363_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_375_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec_ref_known(v___x_379_, 1);
v___x_380_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_381_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_380_, v_a_375_, v_a_376_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_sourceTypes_386_; lean_object* v___x_388_; 
v_sourceTypes_386_ = lean_ctor_get(v_a_382_, 4);
lean_inc(v_sourceTypes_386_);
lean_dec(v_a_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v_sourceTypes_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_sourceTypes_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_391_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_381_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_381_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_379_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_379_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg___boxed(lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes(lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_412_, v_a_420_, v_a_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___boxed(lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes(v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec(v_a_424_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(lean_object* v_e_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_437_, v_a_445_, v_a_446_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_484_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_484_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_484_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_484_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
if (lean_obj_tag(v_a_449_) == 0)
{
lean_object* v___x_453_; 
lean_del_object(v___x_451_);
lean_inc_ref(v_e_436_);
v___x_453_ = l_Lean_Meta_Sym_inferType(v_e_436_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_471_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_471_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_471_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_471_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Expr_getAppFn(v_a_454_);
lean_dec(v_a_454_);
if (lean_obj_tag(v___x_458_) == 4)
{
lean_object* v_declName_459_; uint8_t v___x_460_; 
v_declName_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_declName_459_);
lean_dec_ref_known(v___x_458_, 2);
v___x_460_ = l_Lean_NameSet_contains(v_a_449_, v_declName_459_);
lean_dec(v_declName_459_);
lean_dec_ref_known(v_a_449_, 5);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_463_; 
lean_dec_ref(v_e_436_);
v___x_461_ = lean_box(0);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_461_);
v___x_463_ = v___x_456_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_del_object(v___x_456_);
v___x_465_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_466_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_465_, v_e_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
return v___x_466_;
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_dec_ref(v___x_458_);
lean_dec_ref_known(v_a_449_, 5);
lean_dec_ref(v_e_436_);
v___x_467_ = lean_box(0);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_467_);
v___x_469_ = v___x_456_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref_known(v_a_449_, 5);
lean_dec_ref(v_e_436_);
v_a_472_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_453_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_453_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec_ref(v_e_436_);
v___x_480_ = lean_box(0);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_480_);
v___x_482_ = v___x_451_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
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
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v_e_436_);
v_a_485_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_448_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_448_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm___boxed(lean_object* v_e_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(v_e_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec(v_a_494_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(lean_object* v_msgData_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; lean_object* v_env_513_; lean_object* v___x_514_; lean_object* v_mctx_515_; lean_object* v_lctx_516_; lean_object* v_options_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_512_ = lean_st_ref_get(v___y_510_);
v_env_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc_ref(v_env_513_);
lean_dec(v___x_512_);
v___x_514_ = lean_st_ref_get(v___y_508_);
v_mctx_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_mctx_515_);
lean_dec(v___x_514_);
v_lctx_516_ = lean_ctor_get(v___y_507_, 2);
v_options_517_ = lean_ctor_get(v___y_509_, 2);
lean_inc_ref(v_options_517_);
lean_inc_ref(v_lctx_516_);
v___x_518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_518_, 0, v_env_513_);
lean_ctor_set(v___x_518_, 1, v_mctx_515_);
lean_ctor_set(v___x_518_, 2, v_lctx_516_);
lean_ctor_set(v___x_518_, 3, v_options_517_);
v___x_519_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v_msgData_506_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0___boxed(lean_object* v_msgData_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(v_msgData_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_527_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_528_; double v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_float_of_nat(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(lean_object* v_cls_533_, lean_object* v_msg_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_ref_540_; lean_object* v___x_541_; lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_586_; 
v_ref_540_ = lean_ctor_get(v___y_537_, 5);
v___x_541_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(v_msg_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_586_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_586_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_586_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v_traceState_547_; lean_object* v_env_548_; lean_object* v_nextMacroScope_549_; lean_object* v_ngen_550_; lean_object* v_auxDeclNGen_551_; lean_object* v_cache_552_; lean_object* v_messages_553_; lean_object* v_infoState_554_; lean_object* v_snapshotTasks_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_585_; 
v___x_546_ = lean_st_ref_take(v___y_538_);
v_traceState_547_ = lean_ctor_get(v___x_546_, 4);
v_env_548_ = lean_ctor_get(v___x_546_, 0);
v_nextMacroScope_549_ = lean_ctor_get(v___x_546_, 1);
v_ngen_550_ = lean_ctor_get(v___x_546_, 2);
v_auxDeclNGen_551_ = lean_ctor_get(v___x_546_, 3);
v_cache_552_ = lean_ctor_get(v___x_546_, 5);
v_messages_553_ = lean_ctor_get(v___x_546_, 6);
v_infoState_554_ = lean_ctor_get(v___x_546_, 7);
v_snapshotTasks_555_ = lean_ctor_get(v___x_546_, 8);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_585_ == 0)
{
v___x_557_ = v___x_546_;
v_isShared_558_ = v_isSharedCheck_585_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_snapshotTasks_555_);
lean_inc(v_infoState_554_);
lean_inc(v_messages_553_);
lean_inc(v_cache_552_);
lean_inc(v_traceState_547_);
lean_inc(v_auxDeclNGen_551_);
lean_inc(v_ngen_550_);
lean_inc(v_nextMacroScope_549_);
lean_inc(v_env_548_);
lean_dec(v___x_546_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_585_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint64_t v_tid_559_; lean_object* v_traces_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_584_; 
v_tid_559_ = lean_ctor_get_uint64(v_traceState_547_, sizeof(void*)*1);
v_traces_560_ = lean_ctor_get(v_traceState_547_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_traceState_547_);
if (v_isSharedCheck_584_ == 0)
{
v___x_562_ = v_traceState_547_;
v_isShared_563_ = v_isSharedCheck_584_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_traces_560_);
lean_dec(v_traceState_547_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_584_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; double v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_564_ = lean_box(0);
v___x_565_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0);
v___x_566_ = 0;
v___x_567_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__1));
v___x_568_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_568_, 0, v_cls_533_);
lean_ctor_set(v___x_568_, 1, v___x_564_);
lean_ctor_set(v___x_568_, 2, v___x_567_);
lean_ctor_set_float(v___x_568_, sizeof(void*)*3, v___x_565_);
lean_ctor_set_float(v___x_568_, sizeof(void*)*3 + 8, v___x_565_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*3 + 16, v___x_566_);
v___x_569_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__2));
v___x_570_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v_a_542_);
lean_ctor_set(v___x_570_, 2, v___x_569_);
lean_inc(v_ref_540_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_ref_540_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Lean_PersistentArray_push___redArg(v_traces_560_, v___x_571_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_572_);
v___x_574_ = v___x_562_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_572_);
lean_ctor_set_uint64(v_reuseFailAlloc_583_, sizeof(void*)*1, v_tid_559_);
v___x_574_ = v_reuseFailAlloc_583_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 4, v___x_574_);
v___x_576_ = v___x_557_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_env_548_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_nextMacroScope_549_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_ngen_550_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v_auxDeclNGen_551_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_582_, 5, v_cache_552_);
lean_ctor_set(v_reuseFailAlloc_582_, 6, v_messages_553_);
lean_ctor_set(v_reuseFailAlloc_582_, 7, v_infoState_554_);
lean_ctor_set(v_reuseFailAlloc_582_, 8, v_snapshotTasks_555_);
v___x_576_ = v_reuseFailAlloc_582_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = lean_st_ref_put(v___y_538_, v___x_576_);
v___x_578_ = lean_box(0);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_578_);
v___x_580_ = v___x_544_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___boxed(lean_object* v_cls_587_, lean_object* v_msg_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v_cls_587_, v_msg_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_594_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_));
v___x_599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1));
v___x_600_ = l_Lean_Name_append(v___x_599_, v___x_598_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(lean_object* v_generation_601_, lean_object* v_as_602_, size_t v_sz_603_, size_t v_i_604_, lean_object* v_b_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_604_, v_sz_603_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_dec(v_generation_601_);
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_b_605_);
return v___x_618_;
}
else
{
lean_object* v_a_619_; lean_object* v_options_620_; lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v_inheritedTraceOptions_623_; uint8_t v_hasTrace_624_; lean_object* v___x_625_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; 
v_a_619_ = lean_array_uget_borrowed(v_as_602_, v_i_604_);
v_options_620_ = lean_ctor_get(v___y_614_, 2);
v_fst_621_ = lean_ctor_get(v_a_619_, 0);
v_snd_622_ = lean_ctor_get(v_a_619_, 1);
v_inheritedTraceOptions_623_ = lean_ctor_get(v___y_614_, 13);
v_hasTrace_624_ = lean_ctor_get_uint8(v_options_620_, sizeof(void*)*1);
v___x_625_ = lean_box(0);
if (v_hasTrace_624_ == 0)
{
v___y_627_ = v___y_606_;
v___y_628_ = v___y_607_;
v___y_629_ = v___y_608_;
v___y_630_ = v___y_609_;
v___y_631_ = v___y_610_;
v___y_632_ = v___y_611_;
v___y_633_ = v___y_612_;
v___y_634_ = v___y_613_;
v___y_635_ = v___y_614_;
v___y_636_ = v___y_615_;
goto v___jp_626_;
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_));
v___x_644_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2);
v___x_645_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_623_, v_options_620_, v___x_644_);
if (v___x_645_ == 0)
{
v___y_627_ = v___y_606_;
v___y_628_ = v___y_607_;
v___y_629_ = v___y_608_;
v___y_630_ = v___y_609_;
v___y_631_ = v___y_610_;
v___y_632_ = v___y_611_;
v___y_633_ = v___y_612_;
v___y_634_ = v___y_613_;
v___y_635_ = v___y_614_;
v___y_636_ = v___y_615_;
goto v___jp_626_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Meta_Grind_updateLastTag(v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec_ref_known(v___x_646_, 1);
lean_inc(v_snd_622_);
v___x_647_ = l_Lean_MessageData_ofExpr(v_snd_622_);
v___x_648_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_643_, v___x_647_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_dec_ref_known(v___x_648_, 1);
v___y_627_ = v___y_606_;
v___y_628_ = v___y_607_;
v___y_629_ = v___y_608_;
v___y_630_ = v___y_609_;
v___y_631_ = v___y_610_;
v___y_632_ = v___y_611_;
v___y_633_ = v___y_612_;
v___y_634_ = v___y_613_;
v___y_635_ = v___y_614_;
v___y_636_ = v___y_615_;
goto v___jp_626_;
}
else
{
lean_dec(v_generation_601_);
return v___x_648_;
}
}
else
{
lean_dec(v_generation_601_);
return v___x_646_;
}
}
}
v___jp_626_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_box(6);
v___x_638_ = lean_box(1);
lean_inc(v_generation_601_);
lean_inc(v_snd_622_);
lean_inc(v_fst_621_);
v___x_639_ = l_Lean_Meta_Grind_addNewRawFact(v_fst_621_, v_snd_622_, v_generation_601_, v___x_637_, v___x_638_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_639_) == 0)
{
size_t v___x_640_; size_t v___x_641_; 
lean_dec_ref_known(v___x_639_, 1);
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_add(v_i_604_, v___x_640_);
v_i_604_ = v___x_641_;
v_b_605_ = v___x_625_;
goto _start;
}
else
{
lean_dec(v_generation_601_);
return v___x_639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___boxed(lean_object* v_generation_649_, lean_object* v_as_650_, lean_object* v_sz_651_, lean_object* v_i_652_, lean_object* v_b_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
size_t v_sz_boxed_665_; size_t v_i_boxed_666_; lean_object* v_res_667_; 
v_sz_boxed_665_ = lean_unbox_usize(v_sz_651_);
lean_dec(v_sz_651_);
v_i_boxed_666_ = lean_unbox_usize(v_i_652_);
lean_dec(v_i_652_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(v_generation_649_, v_as_650_, v_sz_boxed_665_, v_i_boxed_666_, v_b_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v_as_650_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(lean_object* v_e_668_, lean_object* v_generation_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Expr_getAppFn(v_e_668_);
if (lean_obj_tag(v___x_681_) == 4)
{
lean_object* v_declName_682_; lean_object* v___x_683_; 
v_declName_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_declName_682_);
lean_dec_ref_known(v___x_681_, 2);
v___x_683_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_670_, v_a_678_, v_a_679_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_715_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_715_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_715_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_715_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
uint8_t v___x_688_; 
v___x_688_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_682_, v_a_684_);
lean_dec(v_a_684_);
lean_dec(v_declName_682_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_691_; 
lean_dec(v_generation_669_);
lean_dec_ref(v_e_668_);
v___x_689_ = lean_box(0);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_689_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
else
{
lean_object* v___x_693_; 
lean_del_object(v___x_686_);
v___x_693_ = l_Lean_Meta_Grind_mkHomoPredInstances(v_e_668_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; size_t v_sz_696_; size_t v___x_697_; lean_object* v___x_698_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = lean_box(0);
v_sz_696_ = lean_array_size(v_a_694_);
v___x_697_ = ((size_t)0ULL);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(v_generation_669_, v_a_694_, v_sz_696_, v___x_697_, v___x_695_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_694_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v___x_698_, 0);
lean_dec(v_unused_706_);
v___x_700_ = v___x_698_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_dec(v___x_698_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_695_);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_695_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
return v___x_698_;
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_generation_669_);
v_a_707_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_693_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_693_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_declName_682_);
lean_dec(v_generation_669_);
lean_dec_ref(v_e_668_);
v_a_716_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_683_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_683_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec_ref(v___x_681_);
lean_dec(v_generation_669_);
lean_dec_ref(v_e_668_);
v___x_724_ = lean_box(0);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds___boxed(lean_object* v_e_726_, lean_object* v_generation_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(v_e_726_, v_generation_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec(v_a_728_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0(lean_object* v_cls_740_, lean_object* v_msg_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v_cls_740_, v_msg_741_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___boxed(lean_object* v_cls_754_, lean_object* v_msg_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0(v_cls_754_, v_msg_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
return v_res_767_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_768_, lean_object* v_i_769_, lean_object* v_k_770_){
_start:
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = lean_array_get_size(v_keys_768_);
v___x_772_ = lean_nat_dec_lt(v_i_769_, v___x_771_);
if (v___x_772_ == 0)
{
lean_dec(v_i_769_);
return v___x_772_;
}
else
{
lean_object* v_k_x27_773_; size_t v___x_774_; size_t v___x_775_; uint8_t v___x_776_; 
v_k_x27_773_ = lean_array_fget_borrowed(v_keys_768_, v_i_769_);
v___x_774_ = lean_ptr_addr(v_k_770_);
v___x_775_ = lean_ptr_addr(v_k_x27_773_);
v___x_776_ = lean_usize_dec_eq(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = lean_nat_add(v_i_769_, v___x_777_);
lean_dec(v_i_769_);
v_i_769_ = v___x_778_;
goto _start;
}
else
{
lean_dec(v_i_769_);
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_780_, lean_object* v_i_781_, lean_object* v_k_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_keys_780_, v_i_781_, v_k_782_);
lean_dec_ref(v_k_782_);
lean_dec_ref(v_keys_780_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(lean_object* v_x_785_, size_t v_x_786_, lean_object* v_x_787_){
_start:
{
if (lean_obj_tag(v_x_785_) == 0)
{
lean_object* v_es_788_; lean_object* v___x_789_; size_t v___x_790_; size_t v___x_791_; lean_object* v_j_792_; lean_object* v___x_793_; 
v_es_788_ = lean_ctor_get(v_x_785_, 0);
v___x_789_ = lean_box(2);
v___x_790_ = ((size_t)31ULL);
v___x_791_ = lean_usize_land(v_x_786_, v___x_790_);
v_j_792_ = lean_usize_to_nat(v___x_791_);
v___x_793_ = lean_array_get_borrowed(v___x_789_, v_es_788_, v_j_792_);
lean_dec(v_j_792_);
switch(lean_obj_tag(v___x_793_))
{
case 0:
{
lean_object* v_key_794_; size_t v___x_795_; size_t v___x_796_; uint8_t v___x_797_; 
v_key_794_ = lean_ctor_get(v___x_793_, 0);
v___x_795_ = lean_ptr_addr(v_x_787_);
v___x_796_ = lean_ptr_addr(v_key_794_);
v___x_797_ = lean_usize_dec_eq(v___x_795_, v___x_796_);
return v___x_797_;
}
case 1:
{
lean_object* v_node_798_; size_t v___x_799_; size_t v___x_800_; 
v_node_798_ = lean_ctor_get(v___x_793_, 0);
v___x_799_ = ((size_t)5ULL);
v___x_800_ = lean_usize_shift_right(v_x_786_, v___x_799_);
v_x_785_ = v_node_798_;
v_x_786_ = v___x_800_;
goto _start;
}
default: 
{
uint8_t v___x_802_; 
v___x_802_ = 0;
return v___x_802_;
}
}
}
else
{
lean_object* v_ks_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_ks_803_ = lean_ctor_get(v_x_785_, 0);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_ks_803_, v___x_804_, v_x_787_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg___boxed(lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
size_t v_x_5718__boxed_809_; uint8_t v_res_810_; lean_object* v_r_811_; 
v_x_5718__boxed_809_ = lean_unbox_usize(v_x_807_);
lean_dec(v_x_807_);
v_res_810_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_806_, v_x_5718__boxed_809_, v_x_808_);
lean_dec_ref(v_x_808_);
lean_dec_ref(v_x_806_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; uint64_t v___x_817_; size_t v___x_818_; uint8_t v___x_819_; 
v___x_814_ = lean_ptr_addr(v_x_813_);
v___x_815_ = ((size_t)3ULL);
v___x_816_ = lean_usize_shift_right(v___x_814_, v___x_815_);
v___x_817_ = lean_usize_to_uint64(v___x_816_);
v___x_818_ = lean_uint64_to_usize(v___x_817_);
v___x_819_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_812_, v___x_818_, v_x_813_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg___boxed(lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_x_820_, v_x_821_);
lean_dec_ref(v_x_821_);
lean_dec_ref(v_x_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(lean_object* v_a_824_, lean_object* v___x_825_, lean_object* v_val_826_, lean_object* v_e_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; 
lean_inc_ref(v_e_827_);
v___x_838_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_824_, v___x_825_, v_e_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
if (lean_obj_tag(v_a_839_) == 0)
{
uint8_t v_done_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_858_; 
v_done_840_ = lean_ctor_get_uint8(v_a_839_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_a_839_);
if (v_isSharedCheck_858_ == 0)
{
v___x_842_ = v_a_839_;
v_isShared_843_ = v_isSharedCheck_858_;
goto v_resetjp_841_;
}
else
{
lean_dec(v_a_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_858_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
if (v_done_840_ == 0)
{
lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_856_; 
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v___x_838_, 0);
lean_dec(v_unused_857_);
v___x_845_ = v___x_838_;
v_isShared_846_ = v_isSharedCheck_856_;
goto v_resetjp_844_;
}
else
{
lean_dec(v___x_838_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_856_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_toGoalState_847_; lean_object* v_enodeMap_848_; uint8_t v___x_849_; lean_object* v___x_851_; 
v_toGoalState_847_ = lean_ctor_get(v_val_826_, 0);
v_enodeMap_848_ = lean_ctor_get(v_toGoalState_847_, 1);
v___x_849_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_enodeMap_848_, v_e_827_);
lean_dec_ref(v_e_827_);
if (v_isShared_843_ == 0)
{
v___x_851_ = v___x_842_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 0, 2);
v___x_851_ = v_reuseFailAlloc_855_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
lean_ctor_set_uint8(v___x_851_, 0, v___x_849_);
lean_ctor_set_uint8(v___x_851_, 1, v_done_840_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_851_);
v___x_853_ = v___x_845_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
lean_del_object(v___x_842_);
lean_dec_ref(v_e_827_);
return v___x_838_;
}
}
}
else
{
lean_dec(v_a_839_);
lean_dec_ref(v_e_827_);
return v___x_838_;
}
}
else
{
lean_dec_ref(v_e_827_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed(lean_object* v_a_859_, lean_object* v___x_860_, lean_object* v_val_861_, lean_object* v_e_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(v_a_859_, v___x_860_, v_val_861_, v_e_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v_val_861_);
lean_dec_ref(v_a_859_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_st_ref_get(v_a_875_);
v___x_880_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_890_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_890_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_890_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_890_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___f_886_; lean_object* v___x_888_; 
v___x_885_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0));
v___f_886_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_886_, 0, v_a_881_);
lean_closure_set(v___f_886_, 1, v___x_885_);
lean_closure_set(v___f_886_, 2, v___x_879_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___f_886_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___f_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec(v___x_879_);
v_a_891_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_880_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_880_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___boxed(lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_899_, v_a_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter(lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_904_, v_a_912_, v_a_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___boxed(lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter(v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec(v_a_916_);
return v_res_927_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0(lean_object* v_00_u03b2_928_, lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_x_929_, v_x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___boxed(lean_object* v_00_u03b2_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
uint8_t v_res_935_; lean_object* v_r_936_; 
v_res_935_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0(v_00_u03b2_932_, v_x_933_, v_x_934_);
lean_dec_ref(v_x_934_);
lean_dec_ref(v_x_933_);
v_r_936_ = lean_box(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, size_t v_x_939_, lean_object* v_x_940_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_938_, v_x_939_, v_x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___boxed(lean_object* v_00_u03b2_942_, lean_object* v_x_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
size_t v_x_5918__boxed_946_; uint8_t v_res_947_; lean_object* v_r_948_; 
v_x_5918__boxed_946_ = lean_unbox_usize(v_x_944_);
lean_dec(v_x_944_);
v_res_947_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0(v_00_u03b2_942_, v_x_943_, v_x_5918__boxed_946_, v_x_945_);
lean_dec_ref(v_x_945_);
lean_dec_ref(v_x_943_);
v_r_948_ = lean_box(v_res_947_);
return v_r_948_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_949_, lean_object* v_keys_950_, lean_object* v_vals_951_, lean_object* v_heq_952_, lean_object* v_i_953_, lean_object* v_k_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_keys_950_, v_i_953_, v_k_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_956_, lean_object* v_keys_957_, lean_object* v_vals_958_, lean_object* v_heq_959_, lean_object* v_i_960_, lean_object* v_k_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1(v_00_u03b2_956_, v_keys_957_, v_vals_958_, v_heq_959_, v_i_960_, v_k_961_);
lean_dec_ref(v_k_961_);
lean_dec_ref(v_vals_958_);
lean_dec_ref(v_keys_957_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__0(lean_object* v_s_964_){
_start:
{
lean_object* v_internalized_965_; uint8_t v_initialized_966_; lean_object* v_thms_967_; lean_object* v_preds_968_; lean_object* v_sourceTypes_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_977_; 
v_internalized_965_ = lean_ctor_get(v_s_964_, 1);
v_initialized_966_ = lean_ctor_get_uint8(v_s_964_, sizeof(void*)*5);
v_thms_967_ = lean_ctor_get(v_s_964_, 2);
v_preds_968_ = lean_ctor_get(v_s_964_, 3);
v_sourceTypes_969_ = lean_ctor_get(v_s_964_, 4);
v_isSharedCheck_977_ = !lean_is_exclusive(v_s_964_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v_s_964_, 0);
lean_dec(v_unused_978_);
v___x_971_ = v_s_964_;
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_sourceTypes_969_);
lean_inc(v_preds_968_);
lean_inc(v_thms_967_);
lean_inc(v_internalized_965_);
lean_dec(v_s_964_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_internalized_965_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_thms_967_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_preds_968_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_sourceTypes_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_976_, sizeof(void*)*5, v_initialized_966_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1(lean_object* v_snd_979_, lean_object* v_s_980_){
_start:
{
lean_object* v_persistentCache_981_; lean_object* v_internalized_982_; uint8_t v_initialized_983_; lean_object* v_thms_984_; lean_object* v_preds_985_; lean_object* v_sourceTypes_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
v_persistentCache_981_ = lean_ctor_get(v_snd_979_, 1);
v_internalized_982_ = lean_ctor_get(v_s_980_, 1);
v_initialized_983_ = lean_ctor_get_uint8(v_s_980_, sizeof(void*)*5);
v_thms_984_ = lean_ctor_get(v_s_980_, 2);
v_preds_985_ = lean_ctor_get(v_s_980_, 3);
v_sourceTypes_986_ = lean_ctor_get(v_s_980_, 4);
v_isSharedCheck_993_ = !lean_is_exclusive(v_s_980_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v_s_980_, 0);
lean_dec(v_unused_994_);
v___x_988_ = v_s_980_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_sourceTypes_986_);
lean_inc(v_preds_985_);
lean_inc(v_thms_984_);
lean_inc(v_internalized_982_);
lean_dec(v_s_980_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
lean_inc_ref(v_persistentCache_981_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v_persistentCache_981_);
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_persistentCache_981_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_internalized_982_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_thms_984_);
lean_ctor_set(v_reuseFailAlloc_992_, 3, v_preds_985_);
lean_ctor_set(v_reuseFailAlloc_992_, 4, v_sourceTypes_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_992_, sizeof(void*)*5, v_initialized_983_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1___boxed(lean_object* v_snd_995_, lean_object* v_s_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1(v_snd_995_, v_s_996_);
lean_dec_ref(v_snd_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(lean_object* v_e_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_1003_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_n(v_a_1012_, 2);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_a_1012_);
lean_ctor_set(v___x_1013_, 1, v_a_1012_);
v___x_1014_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_1015_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_1014_, v_a_1003_, v_a_1008_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___f_1017_; lean_object* v___x_1018_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___f_1017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__0));
v___x_1018_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1014_, v___f_1017_, v_a_1003_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_cache_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_dec_ref_known(v___x_1018_, 1);
v_cache_1019_ = lean_ctor_get(v_a_1016_, 0);
lean_inc_ref(v_cache_1019_);
lean_dec(v_a_1016_);
v___x_1020_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1020_, 0, v_e_1002_);
v___x_1021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__1));
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_1024_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v_cache_1019_);
lean_ctor_set(v___x_1024_, 2, v___x_1023_);
lean_ctor_set(v___x_1024_, 3, v___x_1023_);
v___x_1025_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_1020_, v___x_1013_, v___x_1021_, v___x_1024_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1060_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v_fst_1027_ = lean_ctor_get(v_a_1026_, 0);
v_snd_1028_ = lean_ctor_get(v_a_1026_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_a_1026_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1030_ = v_a_1026_;
v_isShared_1031_ = v_isSharedCheck_1060_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_snd_1028_);
lean_inc(v_fst_1027_);
lean_dec(v_a_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1060_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___f_1032_; lean_object* v___x_1033_; 
v___f_1032_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1032_, 0, v_snd_1028_);
v___x_1033_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1014_, v___f_1032_, v_a_1003_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1050_; 
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v___x_1033_, 0);
lean_dec(v_unused_1051_);
v___x_1035_ = v___x_1033_;
v_isShared_1036_ = v_isSharedCheck_1050_;
goto v_resetjp_1034_;
}
else
{
lean_dec(v___x_1033_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1050_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
if (lean_obj_tag(v_fst_1027_) == 1)
{
lean_object* v_e_x27_1037_; lean_object* v_proof_1038_; lean_object* v___x_1040_; 
v_e_x27_1037_ = lean_ctor_get(v_fst_1027_, 0);
lean_inc_ref(v_e_x27_1037_);
v_proof_1038_ = lean_ctor_get(v_fst_1027_, 1);
lean_inc_ref(v_proof_1038_);
lean_dec_ref_known(v_fst_1027_, 2);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v_proof_1038_);
lean_ctor_set(v___x_1030_, 0, v_e_x27_1037_);
v___x_1040_ = v___x_1030_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_e_x27_1037_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_proof_1038_);
v___x_1040_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1041_);
v___x_1043_ = v___x_1035_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_del_object(v___x_1030_);
lean_dec(v_fst_1027_);
v___x_1046_ = lean_box(0);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1046_);
v___x_1048_ = v___x_1035_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_del_object(v___x_1030_);
lean_dec(v_fst_1027_);
v_a_1052_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1033_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1033_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
v_a_1061_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1025_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1025_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec(v_a_1016_);
lean_dec_ref_known(v___x_1013_, 2);
lean_dec_ref(v_e_1002_);
v_a_1069_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1018_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1018_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref_known(v___x_1013_, 2);
lean_dec_ref(v_e_1002_);
v_a_1077_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1015_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1015_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v_e_1002_);
v_a_1085_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1011_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1011_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___boxed(lean_object* v_e_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f(lean_object* v_e_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1103_, v_a_1104_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___boxed(lean_object* v_e_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f(v_e_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec(v_a_1117_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v_ks_1133_; lean_object* v_vs_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1160_; 
v_ks_1133_ = lean_ctor_get(v_x_1129_, 0);
v_vs_1134_ = lean_ctor_get(v_x_1129_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_x_1129_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1136_ = v_x_1129_;
v_isShared_1137_ = v_isSharedCheck_1160_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_vs_1134_);
lean_inc(v_ks_1133_);
lean_dec(v_x_1129_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1160_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_array_get_size(v_ks_1133_);
v___x_1139_ = lean_nat_dec_lt(v_x_1130_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_x_1130_);
v___x_1140_ = lean_array_push(v_ks_1133_, v_x_1131_);
v___x_1141_ = lean_array_push(v_vs_1134_, v_x_1132_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1141_);
lean_ctor_set(v___x_1136_, 0, v___x_1140_);
v___x_1143_ = v___x_1136_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
else
{
lean_object* v_k_x27_1145_; size_t v___x_1146_; size_t v___x_1147_; uint8_t v___x_1148_; 
v_k_x27_1145_ = lean_array_fget_borrowed(v_ks_1133_, v_x_1130_);
v___x_1146_ = lean_ptr_addr(v_x_1131_);
v___x_1147_ = lean_ptr_addr(v_k_x27_1145_);
v___x_1148_ = lean_usize_dec_eq(v___x_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1150_; 
if (v_isShared_1137_ == 0)
{
v___x_1150_ = v___x_1136_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_ks_1133_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_vs_1134_);
v___x_1150_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_add(v_x_1130_, v___x_1151_);
lean_dec(v_x_1130_);
v_x_1129_ = v___x_1150_;
v_x_1130_ = v___x_1152_;
goto _start;
}
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1155_ = lean_array_fset(v_ks_1133_, v_x_1130_, v_x_1131_);
v___x_1156_ = lean_array_fset(v_vs_1134_, v_x_1130_, v_x_1132_);
lean_dec(v_x_1130_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1156_);
lean_ctor_set(v___x_1136_, 0, v___x_1155_);
v___x_1158_ = v___x_1136_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1161_, lean_object* v_k_1162_, lean_object* v_v_1163_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(0u);
v___x_1165_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1161_, v___x_1164_, v_k_1162_, v_v_1163_);
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(lean_object* v_x_1167_, size_t v_x_1168_, size_t v_x_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_){
_start:
{
if (lean_obj_tag(v_x_1167_) == 0)
{
lean_object* v_es_1172_; size_t v___x_1173_; size_t v___x_1174_; lean_object* v_j_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_es_1172_ = lean_ctor_get(v_x_1167_, 0);
v___x_1173_ = ((size_t)31ULL);
v___x_1174_ = lean_usize_land(v_x_1168_, v___x_1173_);
v_j_1175_ = lean_usize_to_nat(v___x_1174_);
v___x_1176_ = lean_array_get_size(v_es_1172_);
v___x_1177_ = lean_nat_dec_lt(v_j_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_dec(v_j_1175_);
lean_dec(v_x_1171_);
lean_dec_ref(v_x_1170_);
return v_x_1167_;
}
else
{
lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1218_; 
lean_inc_ref(v_es_1172_);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_x_1167_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_x_1167_, 0);
lean_dec(v_unused_1219_);
v___x_1179_ = v_x_1167_;
v_isShared_1180_ = v_isSharedCheck_1218_;
goto v_resetjp_1178_;
}
else
{
lean_dec(v_x_1167_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1218_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_v_1181_; lean_object* v___x_1182_; lean_object* v_xs_x27_1183_; lean_object* v___y_1185_; 
v_v_1181_ = lean_array_fget(v_es_1172_, v_j_1175_);
v___x_1182_ = lean_box(0);
v_xs_x27_1183_ = lean_array_fset(v_es_1172_, v_j_1175_, v___x_1182_);
switch(lean_obj_tag(v_v_1181_))
{
case 0:
{
lean_object* v_key_1190_; lean_object* v_val_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1203_; 
v_key_1190_ = lean_ctor_get(v_v_1181_, 0);
v_val_1191_ = lean_ctor_get(v_v_1181_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_v_1181_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1193_ = v_v_1181_;
v_isShared_1194_ = v_isSharedCheck_1203_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_val_1191_);
lean_inc(v_key_1190_);
lean_dec(v_v_1181_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1203_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
size_t v___x_1195_; size_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = lean_ptr_addr(v_x_1170_);
v___x_1196_ = lean_ptr_addr(v_key_1190_);
v___x_1197_ = lean_usize_dec_eq(v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_del_object(v___x_1193_);
v___x_1198_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1190_, v_val_1191_, v_x_1170_, v_x_1171_);
v___x_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
v___y_1185_ = v___x_1199_;
goto v___jp_1184_;
}
else
{
lean_object* v___x_1201_; 
lean_dec(v_val_1191_);
lean_dec(v_key_1190_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v_x_1171_);
lean_ctor_set(v___x_1193_, 0, v_x_1170_);
v___x_1201_ = v___x_1193_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_x_1170_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_x_1171_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
v___y_1185_ = v___x_1201_;
goto v___jp_1184_;
}
}
}
}
case 1:
{
lean_object* v_node_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1216_; 
v_node_1204_ = lean_ctor_get(v_v_1181_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_v_1181_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1206_ = v_v_1181_;
v_isShared_1207_ = v_isSharedCheck_1216_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_node_1204_);
lean_dec(v_v_1181_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1216_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
size_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1208_ = ((size_t)5ULL);
v___x_1209_ = lean_usize_shift_right(v_x_1168_, v___x_1208_);
v___x_1210_ = ((size_t)1ULL);
v___x_1211_ = lean_usize_add(v_x_1169_, v___x_1210_);
v___x_1212_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_node_1204_, v___x_1209_, v___x_1211_, v_x_1170_, v_x_1171_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1212_);
v___x_1214_ = v___x_1206_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
v___y_1185_ = v___x_1214_;
goto v___jp_1184_;
}
}
}
default: 
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_x_1170_);
lean_ctor_set(v___x_1217_, 1, v_x_1171_);
v___y_1185_ = v___x_1217_;
goto v___jp_1184_;
}
}
v___jp_1184_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = lean_array_fset(v_xs_x27_1183_, v_j_1175_, v___y_1185_);
lean_dec(v_j_1175_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1186_);
v___x_1188_ = v___x_1179_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
else
{
lean_object* v_ks_1220_; lean_object* v_vs_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1239_; 
v_ks_1220_ = lean_ctor_get(v_x_1167_, 0);
v_vs_1221_ = lean_ctor_get(v_x_1167_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_x_1167_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1223_ = v_x_1167_;
v_isShared_1224_ = v_isSharedCheck_1239_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_vs_1221_);
lean_inc(v_ks_1220_);
lean_dec(v_x_1167_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1239_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_ks_1220_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_vs_1221_);
v___x_1226_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v_newNode_1227_; size_t v___x_1228_; uint8_t v___x_1229_; 
v_newNode_1227_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(v___x_1226_, v_x_1170_, v_x_1171_);
v___x_1228_ = ((size_t)7ULL);
v___x_1229_ = lean_usize_dec_le(v___x_1228_, v_x_1169_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1227_);
v___x_1231_ = lean_unsigned_to_nat(4u);
v___x_1232_ = lean_nat_dec_lt(v___x_1230_, v___x_1231_);
lean_dec(v___x_1230_);
if (v___x_1232_ == 0)
{
lean_object* v_ks_1233_; lean_object* v_vs_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_ks_1233_ = lean_ctor_get(v_newNode_1227_, 0);
lean_inc_ref(v_ks_1233_);
v_vs_1234_ = lean_ctor_get(v_newNode_1227_, 1);
lean_inc_ref(v_vs_1234_);
lean_dec_ref(v_newNode_1227_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0);
v___x_1237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_x_1169_, v_ks_1233_, v_vs_1234_, v___x_1235_, v___x_1236_);
lean_dec_ref(v_vs_1234_);
lean_dec_ref(v_ks_1233_);
return v___x_1237_;
}
else
{
return v_newNode_1227_;
}
}
else
{
return v_newNode_1227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(size_t v_depth_1240_, lean_object* v_keys_1241_, lean_object* v_vals_1242_, lean_object* v_i_1243_, lean_object* v_entries_1244_){
_start:
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_array_get_size(v_keys_1241_);
v___x_1246_ = lean_nat_dec_lt(v_i_1243_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_dec(v_i_1243_);
return v_entries_1244_;
}
else
{
lean_object* v_k_1247_; lean_object* v_v_1248_; size_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; uint64_t v___x_1252_; size_t v_h_1253_; size_t v___x_1254_; lean_object* v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; size_t v_h_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_k_1247_ = lean_array_fget_borrowed(v_keys_1241_, v_i_1243_);
v_v_1248_ = lean_array_fget_borrowed(v_vals_1242_, v_i_1243_);
v___x_1249_ = lean_ptr_addr(v_k_1247_);
v___x_1250_ = ((size_t)3ULL);
v___x_1251_ = lean_usize_shift_right(v___x_1249_, v___x_1250_);
v___x_1252_ = lean_usize_to_uint64(v___x_1251_);
v_h_1253_ = lean_uint64_to_usize(v___x_1252_);
v___x_1254_ = ((size_t)5ULL);
v___x_1255_ = lean_unsigned_to_nat(1u);
v___x_1256_ = ((size_t)1ULL);
v___x_1257_ = lean_usize_sub(v_depth_1240_, v___x_1256_);
v___x_1258_ = lean_usize_mul(v___x_1254_, v___x_1257_);
v_h_1259_ = lean_usize_shift_right(v_h_1253_, v___x_1258_);
v___x_1260_ = lean_nat_add(v_i_1243_, v___x_1255_);
lean_dec(v_i_1243_);
lean_inc(v_v_1248_);
lean_inc(v_k_1247_);
v___x_1261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_entries_1244_, v_h_1259_, v_depth_1240_, v_k_1247_, v_v_1248_);
v_i_1243_ = v___x_1260_;
v_entries_1244_ = v___x_1261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1263_, lean_object* v_keys_1264_, lean_object* v_vals_1265_, lean_object* v_i_1266_, lean_object* v_entries_1267_){
_start:
{
size_t v_depth_boxed_1268_; lean_object* v_res_1269_; 
v_depth_boxed_1268_ = lean_unbox_usize(v_depth_1263_);
lean_dec(v_depth_1263_);
v_res_1269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1268_, v_keys_1264_, v_vals_1265_, v_i_1266_, v_entries_1267_);
lean_dec_ref(v_vals_1265_);
lean_dec_ref(v_keys_1264_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
size_t v_x_28281__boxed_1275_; size_t v_x_28282__boxed_1276_; lean_object* v_res_1277_; 
v_x_28281__boxed_1275_ = lean_unbox_usize(v_x_1271_);
lean_dec(v_x_1271_);
v_x_28282__boxed_1276_ = lean_unbox_usize(v_x_1272_);
lean_dec(v_x_1272_);
v_res_1277_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1270_, v_x_28281__boxed_1275_, v_x_28282__boxed_1276_, v_x_1273_, v_x_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
size_t v___x_1281_; size_t v___x_1282_; size_t v___x_1283_; uint64_t v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; lean_object* v___x_1287_; 
v___x_1281_ = lean_ptr_addr(v_x_1279_);
v___x_1282_ = ((size_t)3ULL);
v___x_1283_ = lean_usize_shift_right(v___x_1281_, v___x_1282_);
v___x_1284_ = lean_usize_to_uint64(v___x_1283_);
v___x_1285_ = lean_uint64_to_usize(v___x_1284_);
v___x_1286_ = ((size_t)1ULL);
v___x_1287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1278_, v___x_1285_, v___x_1286_, v_x_1279_, v_x_1280_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___lam__0(lean_object* v_e_1288_, lean_object* v_s_1289_){
_start:
{
lean_object* v_cache_1290_; lean_object* v_internalized_1291_; uint8_t v_initialized_1292_; lean_object* v_thms_1293_; lean_object* v_preds_1294_; lean_object* v_sourceTypes_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1304_; 
v_cache_1290_ = lean_ctor_get(v_s_1289_, 0);
v_internalized_1291_ = lean_ctor_get(v_s_1289_, 1);
v_initialized_1292_ = lean_ctor_get_uint8(v_s_1289_, sizeof(void*)*5);
v_thms_1293_ = lean_ctor_get(v_s_1289_, 2);
v_preds_1294_ = lean_ctor_get(v_s_1289_, 3);
v_sourceTypes_1295_ = lean_ctor_get(v_s_1289_, 4);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_s_1289_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1297_ = v_s_1289_;
v_isShared_1298_ = v_isSharedCheck_1304_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_sourceTypes_1295_);
lean_inc(v_preds_1294_);
lean_inc(v_thms_1293_);
lean_inc(v_internalized_1291_);
lean_inc(v_cache_1290_);
lean_dec(v_s_1289_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1304_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1299_ = lean_box(0);
v___x_1300_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(v_internalized_1291_, v_e_1288_, v___x_1299_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 1, v___x_1300_);
v___x_1302_ = v___x_1297_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_cache_1290_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_thms_1293_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_preds_1294_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_sourceTypes_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1303_, sizeof(void*)*5, v_initialized_1292_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1));
v___x_1310_ = l_Lean_Name_append(v___x_1309_, v___x_1308_);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3));
v___x_1313_ = l_Lean_stringToMessageData(v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg(lean_object* v_e_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1317_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1445_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1445_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1445_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
uint8_t v_hom_1331_; 
v_hom_1331_ = lean_ctor_get_uint8(v_a_1327_, sizeof(void*)*14 + 24);
lean_dec(v_a_1327_);
if (v_hom_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
lean_dec_ref(v_e_1314_);
v___x_1332_ = lean_box(0);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1332_);
v___x_1334_ = v___x_1329_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1));
v___x_1337_ = l_Lean_Expr_isAppOf(v_e_1314_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_del_object(v___x_1329_);
v___x_1338_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_1339_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_1338_, v_a_1315_, v_a_1323_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1432_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1432_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1432_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_internalized_1344_; uint8_t v___x_1345_; 
v_internalized_1344_ = lean_ctor_get(v_a_1340_, 1);
lean_inc_ref(v_internalized_1344_);
lean_dec(v_a_1340_);
v___x_1345_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_internalized_1344_, v_e_1314_);
lean_dec_ref(v_internalized_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___f_1346_; lean_object* v___x_1347_; 
lean_del_object(v___x_1342_);
lean_inc_ref(v_e_1314_);
v___f_1346_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Homo_internalize___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1346_, 0, v_e_1314_);
v___x_1347_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1338_, v___f_1346_, v_a_1315_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v___x_1348_; 
lean_dec_ref_known(v___x_1347_, 1);
lean_inc_ref(v_e_1314_);
v___x_1348_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(v_e_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v___x_1349_; 
lean_dec_ref_known(v___x_1348_, 1);
v___x_1349_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
lean_inc_ref(v_e_1314_);
v___x_1351_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1314_, v_a_1315_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
if (lean_obj_tag(v_a_1352_) == 1)
{
lean_object* v_val_1353_; lean_object* v_fst_1354_; lean_object* v_snd_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1410_; 
v_val_1353_ = lean_ctor_get(v_a_1352_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v_a_1352_, 1);
v_fst_1354_ = lean_ctor_get(v_val_1353_, 0);
v_snd_1355_ = lean_ctor_get(v_val_1353_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_val_1353_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1357_ = v_val_1353_;
v_isShared_1358_ = v_isSharedCheck_1410_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_snd_1355_);
lean_inc(v_fst_1354_);
lean_dec(v_val_1353_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1410_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; 
lean_inc(v_a_1324_);
lean_inc_ref(v_a_1323_);
lean_inc(v_a_1322_);
lean_inc_ref(v_a_1321_);
lean_inc(v_a_1320_);
lean_inc_ref(v_a_1319_);
lean_inc(v_a_1318_);
lean_inc_ref(v_a_1317_);
lean_inc(v_a_1316_);
lean_inc(v_a_1315_);
v___x_1359_ = lean_grind_preprocess(v_fst_1354_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc_n(v_a_1360_, 2);
lean_dec_ref_known(v___x_1359_, 1);
v___x_1361_ = l_Lean_Meta_Simp_Result_getProof(v_a_1360_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v___x_1363_ = l_Lean_Meta_mkEqTrans(v_snd_1355_, v_a_1362_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v_expr_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v_expr_1365_ = lean_ctor_get(v_a_1360_, 0);
lean_inc_ref_n(v_expr_1365_, 2);
lean_dec(v_a_1360_);
v___x_1366_ = lean_box(0);
lean_inc(v_a_1324_);
lean_inc_ref(v_a_1323_);
lean_inc(v_a_1322_);
lean_inc_ref(v_a_1321_);
lean_inc(v_a_1320_);
lean_inc_ref(v_a_1319_);
lean_inc(v_a_1318_);
lean_inc_ref(v_a_1317_);
lean_inc(v_a_1316_);
lean_inc(v_a_1315_);
v___x_1367_ = lean_grind_internalize(v_expr_1365_, v_a_1350_, v___x_1366_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_options_1368_; uint8_t v_hasTrace_1369_; 
lean_dec_ref_known(v___x_1367_, 1);
v_options_1368_ = lean_ctor_get(v_a_1323_, 2);
v_hasTrace_1369_ = lean_ctor_get_uint8(v_options_1368_, sizeof(void*)*1);
if (v_hasTrace_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_del_object(v___x_1357_);
v___x_1370_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1314_, v_expr_1365_, v_a_1364_, v___x_1345_, v_a_1315_, v_a_1317_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1370_;
}
else
{
lean_object* v_inheritedTraceOptions_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v_inheritedTraceOptions_1371_ = lean_ctor_get(v_a_1323_, 13);
v___x_1372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1373_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2);
v___x_1374_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1371_, v_options_1368_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_del_object(v___x_1357_);
v___x_1375_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1314_, v_expr_1365_, v_a_1364_, v___x_1345_, v_a_1315_, v_a_1317_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Meta_Grind_updateLastTag(v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec_ref_known(v___x_1376_, 1);
lean_inc_ref(v_e_1314_);
v___x_1377_ = l_Lean_MessageData_ofExpr(v_e_1314_);
v___x_1378_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4);
if (v_isShared_1358_ == 0)
{
lean_ctor_set_tag(v___x_1357_, 7);
lean_ctor_set(v___x_1357_, 1, v___x_1378_);
lean_ctor_set(v___x_1357_, 0, v___x_1377_);
v___x_1380_ = v___x_1357_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_inc_ref(v_expr_1365_);
v___x_1381_ = l_Lean_MessageData_ofExpr(v_expr_1365_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_1372_, v___x_1382_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1384_; 
lean_dec_ref_known(v___x_1383_, 1);
v___x_1384_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1314_, v_expr_1365_, v_a_1364_, v___x_1345_, v_a_1315_, v_a_1317_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1384_;
}
else
{
lean_dec_ref(v_expr_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_e_1314_);
return v___x_1383_;
}
}
}
else
{
lean_dec_ref(v_expr_1365_);
lean_dec(v_a_1364_);
lean_del_object(v___x_1357_);
lean_dec_ref(v_e_1314_);
return v___x_1376_;
}
}
}
}
else
{
lean_dec_ref(v_expr_1365_);
lean_dec(v_a_1364_);
lean_del_object(v___x_1357_);
lean_dec_ref(v_e_1314_);
return v___x_1367_;
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_a_1360_);
lean_del_object(v___x_1357_);
lean_dec(v_a_1350_);
lean_dec_ref(v_e_1314_);
v_a_1386_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1363_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1363_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_a_1360_);
lean_del_object(v___x_1357_);
lean_dec(v_snd_1355_);
lean_dec(v_a_1350_);
lean_dec_ref(v_e_1314_);
v_a_1394_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1361_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1361_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_del_object(v___x_1357_);
lean_dec(v_snd_1355_);
lean_dec(v_a_1350_);
lean_dec_ref(v_e_1314_);
v_a_1402_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1359_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1359_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
else
{
lean_object* v___x_1411_; 
lean_dec(v_a_1352_);
v___x_1411_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(v_e_1314_, v_a_1350_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1411_;
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_a_1350_);
lean_dec_ref(v_e_1314_);
v_a_1412_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1351_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1351_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v_e_1314_);
v_a_1420_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1349_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1349_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
else
{
lean_dec_ref(v_e_1314_);
return v___x_1348_;
}
}
else
{
lean_dec_ref(v_e_1314_);
return v___x_1347_;
}
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
lean_dec_ref(v_e_1314_);
v___x_1428_ = lean_box(0);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1428_);
v___x_1430_ = v___x_1342_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_e_1314_);
v_a_1433_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1339_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1339_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
lean_dec_ref(v_e_1314_);
v___x_1441_ = lean_box(0);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1441_);
v___x_1443_ = v___x_1329_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec_ref(v_e_1314_);
v_a_1446_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1326_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1326_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___boxed(lean_object* v_e_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Meta_Grind_Homo_internalize___redArg(v_e_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec(v_a_1455_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize(lean_object* v_e_1467_, lean_object* v___parent_x3f_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_Meta_Grind_Homo_internalize___redArg(v_e_1467_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___boxed(lean_object* v_e_1481_, lean_object* v___parent_x3f_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Meta_Grind_Homo_internalize(v_e_1481_, v___parent_x3f_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec(v___parent_x3f_1482_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0(lean_object* v_00_u03b2_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(v_x_1496_, v_x_1497_, v_x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0(lean_object* v_00_u03b2_1500_, lean_object* v_x_1501_, size_t v_x_1502_, size_t v_x_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1501_, v_x_1502_, v_x_1503_, v_x_1504_, v_x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_, lean_object* v_x_1511_, lean_object* v_x_1512_){
_start:
{
size_t v_x_28782__boxed_1513_; size_t v_x_28783__boxed_1514_; lean_object* v_res_1515_; 
v_x_28782__boxed_1513_ = lean_unbox_usize(v_x_1509_);
lean_dec(v_x_1509_);
v_x_28783__boxed_1514_ = lean_unbox_usize(v_x_1510_);
lean_dec(v_x_1510_);
v_res_1515_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0(v_00_u03b2_1507_, v_x_1508_, v_x_28782__boxed_1513_, v_x_28783__boxed_1514_, v_x_1511_, v_x_1512_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1516_, lean_object* v_n_1517_, lean_object* v_k_1518_, lean_object* v_v_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(v_n_1517_, v_k_1518_, v_v_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1521_, size_t v_depth_1522_, lean_object* v_keys_1523_, lean_object* v_vals_1524_, lean_object* v_heq_1525_, lean_object* v_i_1526_, lean_object* v_entries_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_depth_1522_, v_keys_1523_, v_vals_1524_, v_i_1526_, v_entries_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1529_, lean_object* v_depth_1530_, lean_object* v_keys_1531_, lean_object* v_vals_1532_, lean_object* v_heq_1533_, lean_object* v_i_1534_, lean_object* v_entries_1535_){
_start:
{
size_t v_depth_boxed_1536_; lean_object* v_res_1537_; 
v_depth_boxed_1536_ = lean_unbox_usize(v_depth_1530_);
lean_dec(v_depth_1530_);
v_res_1537_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2(v_00_u03b2_1529_, v_depth_boxed_1536_, v_keys_1531_, v_vals_1532_, v_heq_1533_, v_i_1534_, v_entries_1535_);
lean_dec_ref(v_vals_1532_);
lean_dec_ref(v_keys_1531_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1538_, lean_object* v_x_1539_, lean_object* v_x_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1539_, v_x_1540_, v_x_1541_, v_x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewEq(lean_object* v_a_1544_, lean_object* v_b_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1548_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1704_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1704_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1704_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
uint8_t v_hom_1562_; 
v_hom_1562_ = lean_ctor_get_uint8(v_a_1558_, sizeof(void*)*14 + 24);
lean_dec(v_a_1558_);
if (v_hom_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
lean_dec_ref(v_b_1545_);
lean_dec_ref(v_a_1544_);
v___x_1563_ = lean_box(0);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1563_);
v___x_1565_ = v___x_1560_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
else
{
lean_object* v___x_1567_; 
lean_del_object(v___x_1560_);
lean_inc_ref(v_b_1545_);
lean_inc_ref(v_a_1544_);
v___x_1567_ = l_Lean_Meta_Grind_hasSameType(v_a_1544_, v_b_1545_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1695_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1695_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1695_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
uint8_t v___x_1572_; 
v___x_1572_ = lean_unbox(v_a_1568_);
lean_dec(v_a_1568_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
lean_dec_ref(v_b_1545_);
lean_dec_ref(v_a_1544_);
v___x_1573_ = lean_box(0);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1573_);
v___x_1575_ = v___x_1570_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
else
{
lean_object* v___x_1577_; 
lean_del_object(v___x_1570_);
lean_inc_ref(v_b_1545_);
lean_inc_ref(v_a_1544_);
v___x_1577_ = l_Lean_Meta_mkEq(v_a_1544_, v_b_1545_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = l_Lean_Meta_Sym_shareCommon(v_a_1578_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc_n(v_a_1580_, 2);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_a_1580_, v_a_1546_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1670_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1670_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1670_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
if (lean_obj_tag(v_a_1582_) == 1)
{
lean_object* v_val_1586_; lean_object* v_fst_1587_; lean_object* v_snd_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1665_; 
lean_del_object(v___x_1584_);
v_val_1586_ = lean_ctor_get(v_a_1582_, 0);
lean_inc(v_val_1586_);
lean_dec_ref_known(v_a_1582_, 1);
v_fst_1587_ = lean_ctor_get(v_val_1586_, 0);
v_snd_1588_ = lean_ctor_get(v_val_1586_, 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_val_1586_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1590_ = v_val_1586_;
v_isShared_1591_ = v_isSharedCheck_1665_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_snd_1588_);
lean_inc(v_fst_1587_);
lean_dec(v_val_1586_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1665_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; 
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc_ref(v_a_1552_);
lean_inc(v_a_1551_);
lean_inc_ref(v_a_1550_);
lean_inc(v_a_1549_);
lean_inc_ref(v_a_1548_);
lean_inc(v_a_1547_);
lean_inc(v_a_1546_);
lean_inc_ref(v_b_1545_);
lean_inc_ref(v_a_1544_);
v___x_1592_ = lean_grind_mk_eq_proof(v_a_1544_, v_b_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1594_ = l_Lean_Meta_mkEqMP(v_snd_1588_, v_a_1593_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___x_1611_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1611_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1544_, v_a_1546_);
lean_dec_ref(v_a_1544_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___x_1613_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1545_, v_a_1546_);
lean_dec_ref(v_b_1545_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___y_1616_; uint8_t v___x_1632_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1632_ = lean_nat_dec_le(v_a_1612_, v_a_1614_);
if (v___x_1632_ == 0)
{
lean_dec(v_a_1614_);
v___y_1616_ = v_a_1612_;
goto v___jp_1615_;
}
else
{
lean_dec(v_a_1612_);
v___y_1616_ = v_a_1614_;
goto v___jp_1615_;
}
v___jp_1615_:
{
lean_object* v_options_1617_; uint8_t v_hasTrace_1618_; 
v_options_1617_ = lean_ctor_get(v_a_1554_, 2);
v_hasTrace_1618_ = lean_ctor_get_uint8(v_options_1617_, sizeof(void*)*1);
if (v_hasTrace_1618_ == 0)
{
lean_del_object(v___x_1590_);
lean_dec(v_a_1580_);
v___y_1597_ = v___y_1616_;
v___y_1598_ = v_a_1546_;
v___y_1599_ = v_a_1547_;
v___y_1600_ = v_a_1548_;
v___y_1601_ = v_a_1549_;
v___y_1602_ = v_a_1550_;
v___y_1603_ = v_a_1551_;
v___y_1604_ = v_a_1552_;
v___y_1605_ = v_a_1553_;
v___y_1606_ = v_a_1554_;
v___y_1607_ = v_a_1555_;
goto v___jp_1596_;
}
else
{
lean_object* v_inheritedTraceOptions_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v_inheritedTraceOptions_1619_ = lean_ctor_get(v_a_1554_, 13);
v___x_1620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1621_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2);
v___x_1622_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1619_, v_options_1617_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_del_object(v___x_1590_);
lean_dec(v_a_1580_);
v___y_1597_ = v___y_1616_;
v___y_1598_ = v_a_1546_;
v___y_1599_ = v_a_1547_;
v___y_1600_ = v_a_1548_;
v___y_1601_ = v_a_1549_;
v___y_1602_ = v_a_1550_;
v___y_1603_ = v_a_1551_;
v___y_1604_ = v_a_1552_;
v___y_1605_ = v_a_1553_;
v___y_1606_ = v_a_1554_;
v___y_1607_ = v_a_1555_;
goto v___jp_1596_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Meta_Grind_updateLastTag(v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
lean_dec_ref_known(v___x_1623_, 1);
v___x_1624_ = l_Lean_MessageData_ofExpr(v_a_1580_);
v___x_1625_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4);
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 7);
lean_ctor_set(v___x_1590_, 1, v___x_1625_);
lean_ctor_set(v___x_1590_, 0, v___x_1624_);
v___x_1627_ = v___x_1590_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_inc(v_fst_1587_);
v___x_1628_ = l_Lean_MessageData_ofExpr(v_fst_1587_);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_1620_, v___x_1629_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_dec_ref_known(v___x_1630_, 1);
v___y_1597_ = v___y_1616_;
v___y_1598_ = v_a_1546_;
v___y_1599_ = v_a_1547_;
v___y_1600_ = v_a_1548_;
v___y_1601_ = v_a_1549_;
v___y_1602_ = v_a_1550_;
v___y_1603_ = v_a_1551_;
v___y_1604_ = v_a_1552_;
v___y_1605_ = v_a_1553_;
v___y_1606_ = v_a_1554_;
v___y_1607_ = v_a_1555_;
goto v___jp_1596_;
}
else
{
lean_dec(v___y_1616_);
lean_dec(v_a_1595_);
lean_dec(v_fst_1587_);
return v___x_1630_;
}
}
}
else
{
lean_dec(v___y_1616_);
lean_dec(v_a_1595_);
lean_del_object(v___x_1590_);
lean_dec(v_fst_1587_);
lean_dec(v_a_1580_);
return v___x_1623_;
}
}
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_a_1612_);
lean_dec(v_a_1595_);
lean_del_object(v___x_1590_);
lean_dec(v_fst_1587_);
lean_dec(v_a_1580_);
v_a_1633_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1613_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1613_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_a_1595_);
lean_del_object(v___x_1590_);
lean_dec(v_fst_1587_);
lean_dec(v_a_1580_);
lean_dec_ref(v_b_1545_);
v_a_1641_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1611_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1611_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
v___jp_1596_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1608_ = lean_box(6);
v___x_1609_ = lean_box(1);
v___x_1610_ = l_Lean_Meta_Grind_addNewRawFact(v_a_1595_, v_fst_1587_, v___y_1597_, v___x_1608_, v___x_1609_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
return v___x_1610_;
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_del_object(v___x_1590_);
lean_dec(v_fst_1587_);
lean_dec(v_a_1580_);
lean_dec_ref(v_b_1545_);
lean_dec_ref(v_a_1544_);
v_a_1649_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1594_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1594_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
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
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
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
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_del_object(v___x_1590_);
lean_dec(v_snd_1588_);
lean_dec(v_fst_1587_);
lean_dec(v_a_1580_);
lean_dec_ref(v_b_1545_);
lean_dec_ref(v_a_1544_);
v_a_1657_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1592_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1592_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
lean_dec(v_a_1582_);
lean_dec(v_a_1580_);
lean_dec_ref(v_b_1545_);
lean_dec_ref(v_a_1544_);
v___x_1666_ = lean_box(0);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1666_);
v___x_1668_ = v___x_1584_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_a_1580_);
lean_dec_ref(v_b_1545_);
lean_dec_ref(v_a_1544_);
v_a_1671_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1581_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1581_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v_b_1545_);
lean_dec_ref(v_a_1544_);
v_a_1679_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1579_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1579_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref(v_b_1545_);
lean_dec_ref(v_a_1544_);
v_a_1687_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1577_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1577_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
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
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v_b_1545_);
lean_dec_ref(v_a_1544_);
v_a_1696_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1567_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1567_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec_ref(v_b_1545_);
lean_dec_ref(v_a_1544_);
v_a_1705_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1557_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1557_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewEq___boxed(lean_object* v_a_1713_, lean_object* v_b_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Meta_Grind_Homo_processNewEq(v_a_1713_, v_b_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
lean_dec(v_a_1716_);
lean_dec(v_a_1715_);
return v_res_1726_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1730_ = lean_box(0);
v___x_1731_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_processNewDiseq___closed__1));
v___x_1732_ = l_Lean_mkConst(v___x_1731_, v___x_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq(lean_object* v_a_1733_, lean_object* v_b_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1737_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1907_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1907_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1907_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
uint8_t v_hom_1751_; 
v_hom_1751_ = lean_ctor_get_uint8(v_a_1747_, sizeof(void*)*14 + 24);
lean_dec(v_a_1747_);
if (v_hom_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1754_; 
lean_dec_ref(v_b_1734_);
lean_dec_ref(v_a_1733_);
v___x_1752_ = lean_box(0);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1752_);
v___x_1754_ = v___x_1749_;
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
else
{
lean_object* v___x_1756_; 
lean_del_object(v___x_1749_);
lean_inc_ref(v_b_1734_);
lean_inc_ref(v_a_1733_);
v___x_1756_ = l_Lean_Meta_Grind_hasSameType(v_a_1733_, v_b_1734_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1898_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1898_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1898_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_unbox(v_a_1757_);
lean_dec(v_a_1757_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_dec_ref(v_b_1734_);
lean_dec_ref(v_a_1733_);
v___x_1762_ = lean_box(0);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1762_);
v___x_1764_ = v___x_1759_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
else
{
lean_object* v___x_1766_; 
lean_del_object(v___x_1759_);
lean_inc_ref(v_b_1734_);
lean_inc_ref(v_a_1733_);
v___x_1766_ = l_Lean_Meta_mkEq(v_a_1733_, v_b_1734_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = l_Lean_Meta_Sym_shareCommon(v_a_1767_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc_n(v_a_1769_, 2);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1770_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_a_1769_, v_a_1735_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1873_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1873_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1873_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
if (lean_obj_tag(v_a_1771_) == 1)
{
lean_object* v_val_1775_; lean_object* v_fst_1776_; lean_object* v_snd_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1868_; 
lean_del_object(v___x_1773_);
v_val_1775_ = lean_ctor_get(v_a_1771_, 0);
lean_inc(v_val_1775_);
lean_dec_ref_known(v_a_1771_, 1);
v_fst_1776_ = lean_ctor_get(v_val_1775_, 0);
v_snd_1777_ = lean_ctor_get(v_val_1775_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_val_1775_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1779_ = v_val_1775_;
v_isShared_1780_ = v_isSharedCheck_1868_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_snd_1777_);
lean_inc(v_fst_1776_);
lean_dec(v_val_1775_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1868_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; 
lean_inc_ref(v_b_1734_);
lean_inc_ref(v_a_1733_);
v___x_1781_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_1733_, v_b_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v___x_1783_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2, &l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2_once, _init_l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2);
v___x_1784_ = l_Lean_Meta_mkCongrArg(v___x_1783_, v_snd_1777_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = l_Lean_Meta_mkEqMP(v_a_1785_, v_a_1782_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___x_1804_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
v___x_1804_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1733_, v_a_1735_);
lean_dec_ref(v_a_1733_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1806_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1734_, v_a_1735_);
lean_dec_ref(v_b_1734_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___y_1809_; uint8_t v___x_1827_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref_known(v___x_1806_, 1);
v___x_1827_ = lean_nat_dec_le(v_a_1805_, v_a_1807_);
if (v___x_1827_ == 0)
{
lean_dec(v_a_1807_);
v___y_1809_ = v_a_1805_;
goto v___jp_1808_;
}
else
{
lean_dec(v_a_1805_);
v___y_1809_ = v_a_1807_;
goto v___jp_1808_;
}
v___jp_1808_:
{
lean_object* v_options_1810_; uint8_t v_hasTrace_1811_; 
v_options_1810_ = lean_ctor_get(v_a_1743_, 2);
v_hasTrace_1811_ = lean_ctor_get_uint8(v_options_1810_, sizeof(void*)*1);
if (v_hasTrace_1811_ == 0)
{
lean_del_object(v___x_1779_);
lean_dec(v_a_1769_);
v___y_1789_ = v___y_1809_;
v___y_1790_ = v_a_1735_;
v___y_1791_ = v_a_1736_;
v___y_1792_ = v_a_1737_;
v___y_1793_ = v_a_1738_;
v___y_1794_ = v_a_1739_;
v___y_1795_ = v_a_1740_;
v___y_1796_ = v_a_1741_;
v___y_1797_ = v_a_1742_;
v___y_1798_ = v_a_1743_;
v___y_1799_ = v_a_1744_;
goto v___jp_1788_;
}
else
{
lean_object* v_inheritedTraceOptions_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v_inheritedTraceOptions_1812_ = lean_ctor_get(v_a_1743_, 13);
v___x_1813_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1814_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2);
v___x_1815_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1812_, v_options_1810_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_del_object(v___x_1779_);
lean_dec(v_a_1769_);
v___y_1789_ = v___y_1809_;
v___y_1790_ = v_a_1735_;
v___y_1791_ = v_a_1736_;
v___y_1792_ = v_a_1737_;
v___y_1793_ = v_a_1738_;
v___y_1794_ = v_a_1739_;
v___y_1795_ = v_a_1740_;
v___y_1796_ = v_a_1741_;
v___y_1797_ = v_a_1742_;
v___y_1798_ = v_a_1743_;
v___y_1799_ = v_a_1744_;
goto v___jp_1788_;
}
else
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_Meta_Grind_updateLastTag(v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_dec_ref_known(v___x_1816_, 1);
v___x_1817_ = l_Lean_mkNot(v_a_1769_);
v___x_1818_ = l_Lean_MessageData_ofExpr(v___x_1817_);
v___x_1819_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4);
if (v_isShared_1780_ == 0)
{
lean_ctor_set_tag(v___x_1779_, 7);
lean_ctor_set(v___x_1779_, 1, v___x_1819_);
lean_ctor_set(v___x_1779_, 0, v___x_1818_);
v___x_1821_ = v___x_1779_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_inc(v_fst_1776_);
v___x_1822_ = l_Lean_mkNot(v_fst_1776_);
v___x_1823_ = l_Lean_MessageData_ofExpr(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1821_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_1813_, v___x_1824_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_dec_ref_known(v___x_1825_, 1);
v___y_1789_ = v___y_1809_;
v___y_1790_ = v_a_1735_;
v___y_1791_ = v_a_1736_;
v___y_1792_ = v_a_1737_;
v___y_1793_ = v_a_1738_;
v___y_1794_ = v_a_1739_;
v___y_1795_ = v_a_1740_;
v___y_1796_ = v_a_1741_;
v___y_1797_ = v_a_1742_;
v___y_1798_ = v_a_1743_;
v___y_1799_ = v_a_1744_;
goto v___jp_1788_;
}
else
{
lean_dec(v___y_1809_);
lean_dec(v_a_1787_);
lean_dec(v_fst_1776_);
return v___x_1825_;
}
}
}
else
{
lean_dec(v___y_1809_);
lean_dec(v_a_1787_);
lean_del_object(v___x_1779_);
lean_dec(v_fst_1776_);
lean_dec(v_a_1769_);
return v___x_1816_;
}
}
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_a_1805_);
lean_dec(v_a_1787_);
lean_del_object(v___x_1779_);
lean_dec(v_fst_1776_);
lean_dec(v_a_1769_);
v_a_1828_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1806_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1806_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_a_1787_);
lean_del_object(v___x_1779_);
lean_dec(v_fst_1776_);
lean_dec(v_a_1769_);
lean_dec_ref(v_b_1734_);
v_a_1836_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1804_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1804_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
v___jp_1788_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1800_ = l_Lean_mkNot(v_fst_1776_);
v___x_1801_ = lean_box(6);
v___x_1802_ = lean_box(1);
v___x_1803_ = l_Lean_Meta_Grind_addNewRawFact(v_a_1787_, v___x_1800_, v___y_1789_, v___x_1801_, v___x_1802_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
return v___x_1803_;
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_del_object(v___x_1779_);
lean_dec(v_fst_1776_);
lean_dec(v_a_1769_);
lean_dec_ref(v_b_1734_);
lean_dec_ref(v_a_1733_);
v_a_1844_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1786_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1786_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_a_1782_);
lean_del_object(v___x_1779_);
lean_dec(v_fst_1776_);
lean_dec(v_a_1769_);
lean_dec_ref(v_b_1734_);
lean_dec_ref(v_a_1733_);
v_a_1852_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1784_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1784_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_del_object(v___x_1779_);
lean_dec(v_snd_1777_);
lean_dec(v_fst_1776_);
lean_dec(v_a_1769_);
lean_dec_ref(v_b_1734_);
lean_dec_ref(v_a_1733_);
v_a_1860_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1781_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1781_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_dec(v_a_1771_);
lean_dec(v_a_1769_);
lean_dec_ref(v_b_1734_);
lean_dec_ref(v_a_1733_);
v___x_1869_ = lean_box(0);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1869_);
v___x_1871_ = v___x_1773_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_a_1769_);
lean_dec_ref(v_b_1734_);
lean_dec_ref(v_a_1733_);
v_a_1874_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1770_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1770_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v_b_1734_);
lean_dec_ref(v_a_1733_);
v_a_1882_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1768_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1768_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v_b_1734_);
lean_dec_ref(v_a_1733_);
v_a_1890_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1766_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1766_);
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
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v_b_1734_);
lean_dec_ref(v_a_1733_);
v_a_1899_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1756_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1756_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v_b_1734_);
lean_dec_ref(v_a_1733_);
v_a_1908_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1746_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1746_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___boxed(lean_object* v_a_1916_, lean_object* v_b_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_Meta_Grind_Homo_processNewDiseq(v_a_1916_, v_b_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
lean_dec(v_a_1925_);
lean_dec_ref(v_a_1924_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec(v_a_1918_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_apply_11(v___y_1931_, v___y_1930_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, lean_box(0));
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec_ref(v___y_1946_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(uint8_t v___x_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_box(v___x_1958_);
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___x_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
uint8_t v___x_1027__boxed_1984_; lean_object* v_res_1985_; 
v___x_1027__boxed_1984_ = lean_unbox(v___x_1972_);
v_res_1985_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___x_1027__boxed_1984_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec(v___y_1973_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object* v___x_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1986_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___x_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___x_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec(v___y_2000_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___f_2027_; lean_object* v___f_2028_; lean_object* v___x_2029_; 
v___f_2022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2023_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_2024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___f_2027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___f_2028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2029_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(v___x_2023_, v___x_2024_, v___x_2025_, v___x_2026_, v___f_2027_, v___f_2022_, v___f_2027_, v___f_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_();
return v_res_2031_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
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
