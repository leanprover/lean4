// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Homo
// Imports: public import Lean.Meta.Sym.Simp.Theorems import Lean.Meta.Sym.Simp.Attr import Lean.Meta.AppBuilder
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpExt(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "homoExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 68, 174, 250, 89, 27, 196, 113)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_homoExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "homoSourceTypesExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 10, 151, 10, 152, 93, 193, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_homoSourceTypesExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "invalid `[grind hom]` theorem, parameter `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` of `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "` is not determined by the left-hand side of the rule"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "invalid `[grind hom]` theorem, `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is conditional: hypothesis"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 229, .m_capacity = 229, .m_length = 226, .m_data = "\nis not determined by the left-hand side and would have to be discharged when the rule is applied. Homomorphism rules must be unconditional; use E-matching attributes such as `[grind =]` or `[grind →]` for conditional theorems"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "invalid `[grind hom]` theorem, the source type of the `=`-injection rule `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is not headed by a constant"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 98, .m_capacity = 98, .m_length = 97, .m_data = "\nhomomorphism rules translate concrete types; generic injections cannot be tracked by the E-graph"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedHomoPredTheorem = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem = (const lean_object*)&l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "homoPredExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 129, 210, 121, 39, 93, 224, 42)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 8, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_homoPredExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_addHomoPredAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.Tactic.Grind.Homo"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Grind.addHomoPredAttr"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "invalid `[grind hom_pred]` theorem, the conclusion of `"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "` does not contain an application whose trailing arguments are the theorem's explicit parameters"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "invalid `[grind hom_pred]` theorem, `"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9;
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 152, .m_capacity = 152, .m_length = 151, .m_data = "` must have at least one explicit parameter; the trigger is inferred from an application whose trailing arguments are the theorem's explicit parameters"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11;
static const lean_array_object l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_addHomoPredAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a proposition"};
static const lean_object* l_Lean_Meta_Grind_addHomoPredAttr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_addHomoPredAttr___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_addHomoPredAttr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addHomoPredAttr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_mkHomoPredInstances___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_mkHomoPredInstances___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkHomoPredInstances___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHomoPredInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHomoPredInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg(lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = l_Lean_Meta_Grind_homoExt;
v___x_18_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_17_, v_a_15_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg___boxed(lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Meta_Grind_getHomoTheorems___redArg(v_a_19_);
lean_dec(v_a_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems(lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Meta_Grind_getHomoTheorems___redArg(v_a_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoTheorems___boxed(lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_getHomoTheorems(v_a_26_, v_a_27_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object* v_x_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v_a_31_);
lean_inc_ref_n(v___x_32_, 2);
v___x_33_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
lean_ctor_set(v___x_33_, 2, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v_x_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(v_x_34_, v_a_35_);
lean_dec_ref(v_x_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object* v___y_37_){
_start:
{
lean_inc(v___y_37_);
return v___y_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(v___y_38_);
lean_dec(v___y_38_);
return v_res_39_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_49_; uint8_t v___x_50_; lean_object* v___f_51_; lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_49_ = lean_box(0);
v___x_50_ = 0;
v___f_51_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___f_52_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_53_ = l_Lean_NameSet_empty;
v___f_54_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_56_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___f_54_);
lean_ctor_set(v___x_56_, 2, v___x_53_);
lean_ctor_set(v___x_56_, 3, v___f_52_);
lean_ctor_set(v___x_56_, 4, v___f_51_);
lean_ctor_set(v___x_56_, 5, v___x_49_);
lean_ctor_set_uint8(v___x_56_, sizeof(void*)*6, v___x_50_);
lean_ctor_set_uint8(v___x_56_, sizeof(void*)*6 + 1, v___x_50_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_);
v___x_59_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg(lean_object* v_a_62_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_env_66_; lean_object* v___x_67_; lean_object* v_ext_68_; lean_object* v_toEnvExtension_69_; lean_object* v_asyncMode_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_64_ = lean_box(1);
v___x_65_ = lean_st_ref_get(v_a_62_);
v_env_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc_ref(v_env_66_);
lean_dec(v___x_65_);
v___x_67_ = l_Lean_Meta_Grind_homoSourceTypesExt;
v_ext_68_ = lean_ctor_get(v___x_67_, 1);
v_toEnvExtension_69_ = lean_ctor_get(v_ext_68_, 0);
v_asyncMode_70_ = lean_ctor_get(v_toEnvExtension_69_, 2);
v___x_71_ = 0;
v___x_72_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_64_, v___x_67_, v_env_66_, v_asyncMode_70_, v___x_71_);
v___x_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg___boxed(lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_74_);
lean_dec(v_a_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes(lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___boxed(lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_Grind_getHomoSourceTypes(v_a_81_, v_a_82_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0(lean_object* v_k_85_, lean_object* v_b_86_, lean_object* v_c_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
lean_inc(v___y_91_);
lean_inc_ref(v___y_90_);
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
v___x_93_ = lean_apply_7(v_k_85_, v_b_86_, v_c_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, lean_box(0));
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0___boxed(lean_object* v_k_94_, lean_object* v_b_95_, lean_object* v_c_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0(v_k_94_, v_b_95_, v_c_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(lean_object* v_type_103_, lean_object* v_k_104_, uint8_t v_cleanupAnnotations_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___f_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___f_111_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_111_, 0, v_k_104_);
v___x_112_ = 0;
v___x_113_ = lean_box(0);
v___x_114_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_112_, v___x_113_, v_type_103_, v___f_111_, v_cleanupAnnotations_105_, v___x_112_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
v_a_123_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_114_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_114_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___boxed(lean_object* v_type_131_, lean_object* v_k_132_, lean_object* v_cleanupAnnotations_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_139_; lean_object* v_res_140_; 
v_cleanupAnnotations_boxed_139_ = lean_unbox(v_cleanupAnnotations_133_);
v_res_140_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v_type_131_, v_k_132_, v_cleanupAnnotations_boxed_139_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8(lean_object* v_00_u03b1_141_, lean_object* v_type_142_, lean_object* v_k_143_, uint8_t v_cleanupAnnotations_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v_type_142_, v_k_143_, v_cleanupAnnotations_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___boxed(lean_object* v_00_u03b1_151_, lean_object* v_type_152_, lean_object* v_k_153_, lean_object* v_cleanupAnnotations_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_160_; lean_object* v_res_161_; 
v_cleanupAnnotations_boxed_160_ = lean_unbox(v_cleanupAnnotations_154_);
v_res_161_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8(v_00_u03b1_151_, v_type_152_, v_k_153_, v_cleanupAnnotations_boxed_160_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
return v_res_161_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(lean_object* v_k_162_, lean_object* v_t_163_){
_start:
{
if (lean_obj_tag(v_t_163_) == 0)
{
lean_object* v_k_164_; lean_object* v_l_165_; lean_object* v_r_166_; uint8_t v___x_167_; 
v_k_164_ = lean_ctor_get(v_t_163_, 1);
v_l_165_ = lean_ctor_get(v_t_163_, 3);
v_r_166_ = lean_ctor_get(v_t_163_, 4);
v___x_167_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_162_, v_k_164_);
switch(v___x_167_)
{
case 0:
{
v_t_163_ = v_l_165_;
goto _start;
}
case 1:
{
uint8_t v___x_169_; 
v___x_169_ = 1;
return v___x_169_;
}
default: 
{
v_t_163_ = v_r_166_;
goto _start;
}
}
}
else
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg___boxed(lean_object* v_k_172_, lean_object* v_t_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v_k_172_, v_t_173_);
lean_dec(v_t_173_);
lean_dec(v_k_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(lean_object* v_msgData_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; lean_object* v_env_183_; uint8_t v___x_184_; lean_object* v_env_185_; lean_object* v___x_186_; lean_object* v_toCold_187_; lean_object* v_mctx_188_; lean_object* v_lctx_189_; lean_object* v_options_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_182_ = lean_st_ref_get(v___y_180_);
v_env_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc_ref(v_env_183_);
lean_dec(v___x_182_);
v___x_184_ = 0;
v_env_185_ = l_Lean_Environment_setRecordingDeps(v_env_183_, v___x_184_);
v___x_186_ = lean_st_ref_get(v___y_178_);
v_toCold_187_ = lean_ctor_get(v___y_179_, 0);
v_mctx_188_ = lean_ctor_get(v___x_186_, 0);
lean_inc_ref(v_mctx_188_);
lean_dec(v___x_186_);
v_lctx_189_ = lean_ctor_get(v___y_177_, 2);
v_options_190_ = lean_ctor_get(v_toCold_187_, 2);
lean_inc_ref(v_options_190_);
lean_inc_ref(v_lctx_189_);
v___x_191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_191_, 0, v_env_185_);
lean_ctor_set(v___x_191_, 1, v_mctx_188_);
lean_ctor_set(v___x_191_, 2, v_lctx_189_);
lean_ctor_set(v___x_191_, 3, v_options_190_);
v___x_192_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_msgData_176_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5___boxed(lean_object* v_msgData_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(v_msgData_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(lean_object* v_msg_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_ref_207_; lean_object* v___x_208_; lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_217_; 
v_ref_207_ = lean_ctor_get(v___y_204_, 2);
v___x_208_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(v_msg_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_217_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
lean_inc(v_ref_207_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v_ref_207_);
lean_ctor_set(v___x_213_, 1, v_a_209_);
if (v_isShared_212_ == 0)
{
lean_ctor_set_tag(v___x_211_, 1);
lean_ctor_set(v___x_211_, 0, v___x_213_);
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg___boxed(lean_object* v_msg_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_224_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__0));
v___x_227_ = l_Lean_stringToMessageData(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__2));
v___x_230_ = l_Lean_stringToMessageData(v___x_229_);
return v___x_230_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__4));
v___x_233_ = l_Lean_stringToMessageData(v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__6));
v___x_236_ = l_Lean_stringToMessageData(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__8));
v___x_239_ = l_Lean_stringToMessageData(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__10));
v___x_242_ = l_Lean_stringToMessageData(v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(lean_object* v___x_243_, lean_object* v_declName_244_, lean_object* v_as_245_, size_t v_sz_246_, size_t v_i_247_, lean_object* v_b_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_a_255_; uint8_t v___x_259_; 
v___x_259_ = lean_usize_dec_lt(v_i_247_, v_sz_246_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v_declName_244_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v_b_248_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v_a_262_; lean_object* v___x_263_; 
v___x_261_ = lean_box(0);
v_a_262_ = lean_array_uget_borrowed(v_as_245_, v_i_247_);
v___x_263_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_a_262_, v___y_249_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; uint8_t v___x_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_263_, 1);
v___x_265_ = l_Lean_LocalDecl_binderInfo(v_a_264_);
lean_dec(v_a_264_);
if (v___x_265_ == 3)
{
v_a_255_ = v___x_261_;
goto v___jp_254_;
}
else
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = l_Lean_Expr_fvarId_x21(v_a_262_);
v___x_267_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_266_, v___x_243_);
lean_dec(v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_inc(v___y_252_);
lean_inc_ref(v___y_251_);
lean_inc(v___y_250_);
lean_inc_ref(v___y_249_);
lean_inc(v_a_262_);
v___x_268_ = lean_infer_type(v_a_262_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_n(v_a_269_, 2);
lean_dec_ref_known(v___x_268_, 1);
v___x_270_ = l_Lean_Meta_isProp(v_a_269_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; uint8_t v___x_272_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = lean_unbox(v_a_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v_a_269_);
v___x_273_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1);
lean_inc(v_a_262_);
v___x_274_ = l_Lean_MessageData_ofExpr(v_a_262_);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3);
v___x_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_unbox(v_a_271_);
lean_dec(v_a_271_);
lean_inc(v_declName_244_);
v___x_279_ = l_Lean_MessageData_ofConstName(v_declName_244_, v___x_278_);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_277_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_282_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_dec_ref_known(v___x_283_, 1);
v_a_255_ = v___x_261_;
goto v___jp_254_;
}
else
{
lean_dec(v_declName_244_);
return v___x_283_;
}
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec(v_a_271_);
v___x_284_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7);
lean_inc(v_declName_244_);
v___x_285_ = l_Lean_MessageData_ofConstName(v_declName_244_, v___x_267_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = l_Lean_indentExpr(v_a_269_);
v___x_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_292_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_dec_ref_known(v___x_293_, 1);
v_a_255_ = v___x_261_;
goto v___jp_254_;
}
else
{
lean_dec(v_declName_244_);
return v___x_293_;
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec(v_a_269_);
lean_dec(v_declName_244_);
v_a_294_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_270_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_270_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec(v_declName_244_);
v_a_302_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_268_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_268_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
else
{
v_a_255_ = v___x_261_;
goto v___jp_254_;
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec(v_declName_244_);
v_a_310_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_263_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_263_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
v___jp_254_:
{
size_t v___x_256_; size_t v___x_257_; 
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_add(v_i_247_, v___x_256_);
v_i_247_ = v___x_257_;
v_b_248_ = v_a_255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___boxed(lean_object* v___x_318_, lean_object* v_declName_319_, lean_object* v_as_320_, lean_object* v_sz_321_, lean_object* v_i_322_, lean_object* v_b_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
size_t v_sz_boxed_329_; size_t v_i_boxed_330_; lean_object* v_res_331_; 
v_sz_boxed_329_ = lean_unbox_usize(v_sz_321_);
lean_dec(v_sz_321_);
v_i_boxed_330_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_res_331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(v___x_318_, v_declName_319_, v_as_320_, v_sz_boxed_329_, v_i_boxed_330_, v_b_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec_ref(v_as_320_);
lean_dec(v___x_318_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(lean_object* v___x_332_, lean_object* v_as_333_, size_t v_sz_334_, size_t v_i_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_usize_dec_lt(v_i_335_, v_sz_334_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec(v___x_332_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v_b_336_);
return v___x_343_;
}
else
{
lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_380_; 
v_fst_344_ = lean_ctor_get(v_b_336_, 0);
v_snd_345_ = lean_ctor_get(v_b_336_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_b_336_);
if (v_isSharedCheck_380_ == 0)
{
v___x_347_ = v_b_336_;
v_isShared_348_ = v_isSharedCheck_380_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snd_345_);
lean_inc(v_fst_344_);
lean_dec(v_b_336_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_380_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_a_349_; lean_object* v___x_350_; 
v_a_349_ = lean_array_uget_borrowed(v_as_333_, v_i_335_);
lean_inc(v___y_340_);
lean_inc_ref(v___y_339_);
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
lean_inc(v_a_349_);
v___x_350_ = lean_infer_type(v_a_349_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_371_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_371_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_371_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_371_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = l_Lean_Expr_fvarId_x21(v_a_349_);
v___x_363_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_362_, v_fst_344_);
lean_dec(v___x_362_);
if (v___x_363_ == 0)
{
lean_del_object(v___x_353_);
lean_dec(v_a_351_);
goto v___jp_355_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = l_Lean_Expr_containsFVar(v_a_351_, v___x_332_);
lean_dec(v_a_351_);
if (v___x_364_ == 0)
{
lean_del_object(v___x_353_);
goto v___jp_355_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
v___x_365_ = l_Lean_FVarIdSet_insert(v_fst_344_, v___x_332_);
v___x_366_ = lean_box(v___x_342_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_367_);
v___x_369_ = v___x_353_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
v___jp_355_:
{
lean_object* v___x_357_; 
if (v_isShared_348_ == 0)
{
v___x_357_ = v___x_347_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_fst_344_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_snd_345_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
size_t v___x_358_; size_t v___x_359_; 
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_add(v_i_335_, v___x_358_);
v_i_335_ = v___x_359_;
v_b_336_ = v___x_357_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
lean_dec(v___x_332_);
v_a_372_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_350_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_350_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1___boxed(lean_object* v___x_381_, lean_object* v_as_382_, lean_object* v_sz_383_, lean_object* v_i_384_, lean_object* v_b_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
size_t v_sz_boxed_391_; size_t v_i_boxed_392_; lean_object* v_res_393_; 
v_sz_boxed_391_ = lean_unbox_usize(v_sz_383_);
lean_dec(v_sz_383_);
v_i_boxed_392_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_res_393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(v___x_381_, v_as_382_, v_sz_boxed_391_, v_i_boxed_392_, v_b_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec_ref(v_as_382_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(lean_object* v_xs_394_, lean_object* v_as_395_, size_t v_sz_396_, size_t v_i_397_, lean_object* v_b_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_a_405_; uint8_t v___x_409_; 
v___x_409_ = lean_usize_dec_lt(v_i_397_, v_sz_396_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v_b_398_);
return v___x_410_;
}
else
{
lean_object* v_fst_411_; lean_object* v_snd_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_438_; 
v_fst_411_ = lean_ctor_get(v_b_398_, 0);
v_snd_412_ = lean_ctor_get(v_b_398_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_b_398_);
if (v_isSharedCheck_438_ == 0)
{
v___x_414_ = v_b_398_;
v_isShared_415_ = v_isSharedCheck_438_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_snd_412_);
lean_inc(v_fst_411_);
lean_dec(v_b_398_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_438_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_a_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_a_416_ = lean_array_uget_borrowed(v_as_395_, v_i_397_);
v___x_417_ = l_Lean_Expr_fvarId_x21(v_a_416_);
v___x_418_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_417_, v_fst_411_);
if (v___x_418_ == 0)
{
lean_object* v___x_420_; 
if (v_isShared_415_ == 0)
{
v___x_420_ = v___x_414_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_fst_411_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_snd_412_);
v___x_420_ = v_reuseFailAlloc_434_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
size_t v_sz_421_; size_t v___x_422_; lean_object* v___x_423_; 
v_sz_421_ = lean_array_size(v_xs_394_);
v___x_422_ = ((size_t)0ULL);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(v___x_417_, v_xs_394_, v_sz_421_, v___x_422_, v___x_420_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v_fst_425_; lean_object* v_snd_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
v_fst_425_ = lean_ctor_get(v_a_424_, 0);
v_snd_426_ = lean_ctor_get(v_a_424_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_a_424_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v_a_424_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_snd_426_);
lean_inc(v_fst_425_);
lean_dec(v_a_424_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_fst_425_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_snd_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
v_a_405_ = v___x_431_;
goto v___jp_404_;
}
}
}
else
{
return v___x_423_;
}
}
}
else
{
lean_object* v___x_436_; 
lean_dec(v___x_417_);
if (v_isShared_415_ == 0)
{
v___x_436_ = v___x_414_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_fst_411_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_snd_412_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
v_a_405_ = v___x_436_;
goto v___jp_404_;
}
}
}
}
v___jp_404_:
{
size_t v___x_406_; size_t v___x_407_; 
v___x_406_ = ((size_t)1ULL);
v___x_407_ = lean_usize_add(v_i_397_, v___x_406_);
v_i_397_ = v___x_407_;
v_b_398_ = v_a_405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2___boxed(lean_object* v_xs_439_, lean_object* v_as_440_, lean_object* v_sz_441_, lean_object* v_i_442_, lean_object* v_b_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
size_t v_sz_boxed_449_; size_t v_i_boxed_450_; lean_object* v_res_451_; 
v_sz_boxed_449_ = lean_unbox_usize(v_sz_441_);
lean_dec(v_sz_441_);
v_i_boxed_450_ = lean_unbox_usize(v_i_442_);
lean_dec(v_i_442_);
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(v_xs_439_, v_as_440_, v_sz_boxed_449_, v_i_boxed_450_, v_b_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec_ref(v_as_440_);
lean_dec_ref(v_xs_439_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(lean_object* v_xs_452_, lean_object* v_a_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_snd_459_; uint8_t v___x_460_; 
v_snd_459_ = lean_ctor_get(v_a_453_, 1);
v___x_460_ = lean_unbox(v_snd_459_);
if (v___x_460_ == 0)
{
lean_object* v_fst_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_469_; 
lean_inc(v_snd_459_);
v_fst_461_ = lean_ctor_get(v_a_453_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v_a_453_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v_a_453_, 1);
lean_dec(v_unused_470_);
v___x_463_ = v_a_453_;
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_fst_461_);
lean_dec(v_a_453_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_469_;
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
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_fst_461_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_snd_459_);
v___x_466_ = v_reuseFailAlloc_468_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
}
else
{
lean_object* v_fst_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_494_; 
v_fst_471_ = lean_ctor_get(v_a_453_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v_a_453_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v_a_453_, 1);
lean_dec(v_unused_495_);
v___x_473_ = v_a_453_;
v_isShared_474_ = v_isSharedCheck_494_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_fst_471_);
lean_dec(v_a_453_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_494_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_475_ = 0;
v___x_476_ = lean_box(v___x_475_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_476_);
v___x_478_ = v___x_473_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_fst_471_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_476_);
v___x_478_ = v_reuseFailAlloc_493_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
size_t v_sz_479_; size_t v___x_480_; lean_object* v___x_481_; 
v_sz_479_ = lean_array_size(v_xs_452_);
v___x_480_ = ((size_t)0ULL);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(v_xs_452_, v_xs_452_, v_sz_479_, v___x_480_, v___x_478_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v_fst_483_; lean_object* v_snd_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_492_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_481_, 1);
v_fst_483_ = lean_ctor_get(v_a_482_, 0);
v_snd_484_ = lean_ctor_get(v_a_482_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_a_482_);
if (v_isSharedCheck_492_ == 0)
{
v___x_486_ = v_a_482_;
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snd_484_);
lean_inc(v_fst_483_);
lean_dec(v_a_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_fst_483_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_snd_484_);
v___x_489_ = v_reuseFailAlloc_491_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
v_a_453_ = v___x_489_;
goto _start;
}
}
}
else
{
return v___x_481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg___boxed(lean_object* v_xs_496_, lean_object* v_a_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_496_, v_a_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec_ref(v_xs_496_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(lean_object* v___y_504_, lean_object* v_as_505_, size_t v_sz_506_, size_t v_i_507_, lean_object* v_b_508_){
_start:
{
lean_object* v_a_511_; uint8_t v___x_515_; 
v___x_515_ = lean_usize_dec_lt(v_i_507_, v_sz_506_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_b_508_);
return v___x_516_;
}
else
{
lean_object* v_a_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_a_517_ = lean_array_uget_borrowed(v_as_505_, v_i_507_);
v___x_518_ = l_Lean_Expr_fvarId_x21(v_a_517_);
v___x_519_ = l_Lean_Expr_containsFVar(v___y_504_, v___x_518_);
if (v___x_519_ == 0)
{
lean_dec(v___x_518_);
v_a_511_ = v_b_508_;
goto v___jp_510_;
}
else
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_FVarIdSet_insert(v_b_508_, v___x_518_);
v_a_511_ = v___x_520_;
goto v___jp_510_;
}
}
v___jp_510_:
{
size_t v___x_512_; size_t v___x_513_; 
v___x_512_ = ((size_t)1ULL);
v___x_513_ = lean_usize_add(v_i_507_, v___x_512_);
v_i_507_ = v___x_513_;
v_b_508_ = v_a_511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg___boxed(lean_object* v___y_521_, lean_object* v_as_522_, lean_object* v_sz_523_, lean_object* v_i_524_, lean_object* v_b_525_, lean_object* v___y_526_){
_start:
{
size_t v_sz_boxed_527_; size_t v_i_boxed_528_; lean_object* v_res_529_; 
v_sz_boxed_527_ = lean_unbox_usize(v_sz_523_);
lean_dec(v_sz_523_);
v_i_boxed_528_ = lean_unbox_usize(v_i_524_);
lean_dec(v_i_524_);
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_521_, v_as_522_, v_sz_boxed_527_, v_i_boxed_528_, v_b_525_);
lean_dec_ref(v_as_522_);
lean_dec_ref(v___y_521_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0(lean_object* v___x_539_, lean_object* v_declName_540_, lean_object* v_xs_541_, lean_object* v_concl_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v___x_548_; uint8_t v___x_549_; uint8_t v___x_550_; lean_object* v___y_552_; 
lean_inc_ref(v_concl_542_);
v___x_548_ = l_Lean_Expr_cleanupAnnotations(v_concl_542_);
v___x_549_ = l_Lean_Expr_isApp(v___x_548_);
v___x_550_ = 1;
if (v___x_549_ == 0)
{
lean_dec_ref(v___x_548_);
v___y_552_ = v_concl_542_;
goto v___jp_551_;
}
else
{
lean_object* v_arg_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_arg_588_ = lean_ctor_get(v___x_548_, 1);
lean_inc_ref(v_arg_588_);
v___x_589_ = l_Lean_Expr_appFnCleanup___redArg(v___x_548_);
v___x_590_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__1));
v___x_591_ = l_Lean_Expr_isConstOf(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
uint8_t v___x_592_; 
lean_dec_ref(v_arg_588_);
v___x_592_ = l_Lean_Expr_isApp(v___x_589_);
if (v___x_592_ == 0)
{
lean_dec_ref(v___x_589_);
v___y_552_ = v_concl_542_;
goto v___jp_551_;
}
else
{
lean_object* v_arg_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_arg_593_ = lean_ctor_get(v___x_589_, 1);
lean_inc_ref(v_arg_593_);
v___x_594_ = l_Lean_Expr_appFnCleanup___redArg(v___x_589_);
v___x_595_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3));
v___x_596_ = l_Lean_Expr_isConstOf(v___x_594_, v___x_595_);
if (v___x_596_ == 0)
{
uint8_t v___x_597_; 
v___x_597_ = l_Lean_Expr_isApp(v___x_594_);
if (v___x_597_ == 0)
{
lean_dec_ref(v___x_594_);
lean_dec_ref(v_arg_593_);
v___y_552_ = v_concl_542_;
goto v___jp_551_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_598_ = l_Lean_Expr_appFnCleanup___redArg(v___x_594_);
v___x_599_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_600_ = l_Lean_Expr_isConstOf(v___x_598_, v___x_599_);
lean_dec_ref(v___x_598_);
if (v___x_600_ == 0)
{
lean_dec_ref(v_arg_593_);
v___y_552_ = v_concl_542_;
goto v___jp_551_;
}
else
{
lean_dec_ref(v_concl_542_);
v___y_552_ = v_arg_593_;
goto v___jp_551_;
}
}
}
else
{
lean_dec_ref(v___x_594_);
lean_dec_ref(v_concl_542_);
v___y_552_ = v_arg_593_;
goto v___jp_551_;
}
}
}
else
{
lean_dec_ref(v___x_589_);
lean_dec_ref(v_concl_542_);
v___y_552_ = v_arg_588_;
goto v___jp_551_;
}
}
v___jp_551_:
{
size_t v_sz_553_; size_t v___x_554_; lean_object* v___x_555_; 
v_sz_553_ = lean_array_size(v_xs_541_);
v___x_554_ = ((size_t)0ULL);
v___x_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_552_, v_xs_541_, v_sz_553_, v___x_554_, v___x_539_);
lean_dec_ref(v___y_552_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v___x_555_, 1);
v___x_557_ = lean_box(v___x_550_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_a_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_541_, v___x_558_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v_fst_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v_fst_561_ = lean_ctor_get(v_a_560_, 0);
lean_inc(v_fst_561_);
lean_dec(v_a_560_);
v___x_562_ = lean_box(0);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(v_fst_561_, v_declName_540_, v_xs_541_, v_sz_553_, v___x_554_, v___x_562_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v_fst_561_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v___x_563_, 0);
lean_dec(v_unused_571_);
v___x_565_ = v___x_563_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_dec(v___x_563_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_562_);
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_562_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
else
{
return v___x_563_;
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec(v_declName_540_);
v_a_572_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_559_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_559_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec(v_declName_540_);
v_a_580_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_555_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_555_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___boxed(lean_object* v___x_601_, lean_object* v_declName_602_, lean_object* v_xs_603_, lean_object* v_concl_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Meta_Grind_validateHomoTheorem___lam__0(v___x_601_, v_declName_602_, v_xs_603_, v_concl_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec_ref(v_xs_603_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(lean_object* v_ref_611_, lean_object* v_msg_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_toCold_618_; lean_object* v_currRecDepth_619_; lean_object* v_ref_620_; uint16_t v_optionFlags_621_; uint8_t v_suppressElabErrors_622_; uint8_t v_isRecordingDeps_623_; lean_object* v_ref_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_toCold_618_ = lean_ctor_get(v___y_615_, 0);
v_currRecDepth_619_ = lean_ctor_get(v___y_615_, 1);
v_ref_620_ = lean_ctor_get(v___y_615_, 2);
v_optionFlags_621_ = lean_ctor_get_uint16(v___y_615_, sizeof(void*)*3);
v_suppressElabErrors_622_ = lean_ctor_get_uint8(v___y_615_, sizeof(void*)*3 + 2);
v_isRecordingDeps_623_ = lean_ctor_get_uint8(v___y_615_, sizeof(void*)*3 + 3);
v_ref_624_ = l_Lean_replaceRef(v_ref_611_, v_ref_620_);
lean_inc(v_currRecDepth_619_);
lean_inc_ref(v_toCold_618_);
v___x_625_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_625_, 0, v_toCold_618_);
lean_ctor_set(v___x_625_, 1, v_currRecDepth_619_);
lean_ctor_set(v___x_625_, 2, v_ref_624_);
lean_ctor_set_uint16(v___x_625_, sizeof(void*)*3, v_optionFlags_621_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*3 + 2, v_suppressElabErrors_622_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*3 + 3, v_isRecordingDeps_623_);
v___x_626_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_612_, v___y_613_, v___y_614_, v___x_625_, v___y_616_);
lean_dec_ref_known(v___x_625_, 3);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg___boxed(lean_object* v_ref_627_, lean_object* v_msg_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_627_, v_msg_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v_ref_627_);
return v_res_634_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_638_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_639_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
lean_ctor_set(v___x_641_, 2, v___x_640_);
lean_ctor_set(v___x_641_, 3, v___x_640_);
lean_ctor_set(v___x_641_, 4, v___x_639_);
lean_ctor_set(v___x_641_, 5, v___x_639_);
lean_ctor_set(v___x_641_, 6, v___x_639_);
lean_ctor_set(v___x_641_, 7, v___x_639_);
lean_ctor_set(v___x_641_, 8, v___x_639_);
lean_ctor_set(v___x_641_, 9, v___x_639_);
lean_ctor_set(v___x_641_, 10, v___x_639_);
lean_ctor_set(v___x_641_, 11, v___x_638_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_unsigned_to_nat(32u);
v___x_643_ = lean_mk_empty_array_with_capacity(v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_645_ = ((size_t)5ULL);
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = lean_unsigned_to_nat(32u);
v___x_648_ = lean_mk_empty_array_with_capacity(v___x_647_);
v___x_649_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_650_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v___x_648_);
lean_ctor_set(v___x_650_, 2, v___x_646_);
lean_ctor_set(v___x_650_, 3, v___x_646_);
lean_ctor_set_usize(v___x_650_, 4, v___x_645_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_651_ = lean_box(1);
v___x_652_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_653_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___x_652_);
lean_ctor_set(v___x_654_, 2, v___x_651_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_666_ = l_Lean_stringToMessageData(v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_669_ = l_Lean_stringToMessageData(v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_672_ = l_Lean_stringToMessageData(v___x_671_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_675_ = l_Lean_stringToMessageData(v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_676_, lean_object* v_declHint_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_env_682_; uint8_t v___x_683_; 
v___x_680_ = lean_box(0);
v___x_681_ = lean_st_ref_get(v___y_678_);
v_env_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref(v_env_682_);
lean_dec(v___x_681_);
v___x_683_ = l_Lean_Name_isAnonymous(v_declHint_677_);
if (v___x_683_ == 0)
{
uint8_t v_isExporting_684_; 
v_isExporting_684_ = lean_ctor_get_uint8(v_env_682_, sizeof(void*)*13);
if (v_isExporting_684_ == 0)
{
lean_object* v___x_685_; 
lean_dec_ref(v_env_682_);
lean_dec(v_declHint_677_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_msg_676_);
return v___x_685_;
}
else
{
lean_object* v___x_686_; uint8_t v___x_687_; 
lean_inc_ref(v_env_682_);
v___x_686_ = l_Lean_Environment_setExporting(v_env_682_, v___x_683_);
lean_inc(v_declHint_677_);
lean_inc_ref(v___x_686_);
v___x_687_ = l_Lean_Environment_contains(v___x_686_, v_declHint_677_, v_isExporting_684_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
lean_dec_ref(v___x_686_);
lean_dec_ref(v_env_682_);
lean_dec(v_declHint_677_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v_msg_676_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_c_694_; lean_object* v___x_695_; 
v___x_689_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_690_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_691_ = l_Lean_Options_empty;
v___x_692_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_692_, 0, v___x_686_);
lean_ctor_set(v___x_692_, 1, v___x_689_);
lean_ctor_set(v___x_692_, 2, v___x_690_);
lean_ctor_set(v___x_692_, 3, v___x_691_);
lean_inc(v_declHint_677_);
v___x_693_ = l_Lean_MessageData_ofConstName(v_declHint_677_, v___x_683_);
v_c_694_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_694_, 0, v___x_692_);
lean_ctor_set(v_c_694_, 1, v___x_693_);
v___x_695_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_682_, v_declHint_677_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec_ref(v_env_682_);
lean_dec(v_declHint_677_);
v___x_696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v_c_694_);
v___x_698_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = l_Lean_MessageData_note(v___x_699_);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v_msg_676_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
else
{
lean_object* v_val_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_737_; 
v_val_703_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_737_ == 0)
{
v___x_705_ = v___x_695_;
v_isShared_706_ = v_isSharedCheck_737_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_val_703_);
lean_dec(v___x_695_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_737_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_mod_709_; uint8_t v___x_710_; 
v___x_707_ = l_Lean_Environment_header(v_env_682_);
lean_dec_ref(v_env_682_);
v___x_708_ = l_Lean_EnvironmentHeader_moduleNames(v___x_707_);
v_mod_709_ = lean_array_get(v___x_680_, v___x_708_, v_val_703_);
lean_dec(v_val_703_);
lean_dec_ref(v___x_708_);
v___x_710_ = l_Lean_isPrivateName(v_declHint_677_);
lean_dec(v_declHint_677_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_711_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v_c_694_);
v___x_713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = l_Lean_MessageData_ofName(v_mod_709_);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l_Lean_MessageData_note(v___x_718_);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v_msg_676_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
if (v_isShared_706_ == 0)
{
lean_ctor_set_tag(v___x_705_, 0);
lean_ctor_set(v___x_705_, 0, v___x_720_);
v___x_722_ = v___x_705_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_724_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v_c_694_);
v___x_726_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = l_Lean_MessageData_ofName(v_mod_709_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_MessageData_note(v___x_731_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v_msg_676_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
if (v_isShared_706_ == 0)
{
lean_ctor_set_tag(v___x_705_, 0);
lean_ctor_set(v___x_705_, 0, v___x_733_);
v___x_735_ = v___x_705_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_738_; 
lean_dec_ref(v_env_682_);
lean_dec(v_declHint_677_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v_msg_676_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_739_, lean_object* v_declHint_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_739_, v_declHint_740_, v___y_741_);
lean_dec(v___y_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_744_, lean_object* v_declHint_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_761_; 
v___x_751_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_744_, v_declHint_745_, v___y_749_);
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_761_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_761_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_761_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_756_ = l_Lean_unknownIdentifierMessageTag;
v___x_757_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v_a_752_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_757_);
v___x_759_ = v___x_754_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_762_, lean_object* v_declHint_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(v_msg_762_, v_declHint_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(lean_object* v_ref_770_, lean_object* v_msg_771_, lean_object* v_declHint_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; lean_object* v_a_779_; lean_object* v___x_780_; 
v___x_778_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(v_msg_771_, v_declHint_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref(v___x_778_);
v___x_780_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_770_, v_a_779_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg___boxed(lean_object* v_ref_781_, lean_object* v_msg_782_, lean_object* v_declHint_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_781_, v_msg_782_, v_declHint_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v_ref_781_);
return v_res_789_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__0));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__2));
v___x_795_ = l_Lean_stringToMessageData(v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_796_, lean_object* v_constName_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_803_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1);
v___x_804_ = 0;
lean_inc(v_constName_797_);
v___x_805_ = l_Lean_MessageData_ofConstName(v_constName_797_, v___x_804_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_803_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_796_, v___x_808_, v_constName_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_810_, lean_object* v_constName_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_810_, v_constName_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v_ref_810_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(lean_object* v_constName_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_ref_824_; lean_object* v___x_825_; 
v_ref_824_ = lean_ctor_get(v___y_821_, 2);
v___x_825_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_824_, v_constName_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg___boxed(lean_object* v_constName_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(lean_object* v_constName_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; lean_object* v_env_840_; uint8_t v___x_841_; lean_object* v___x_842_; 
v___x_839_ = lean_st_ref_get(v___y_837_);
v_env_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc_ref(v_env_840_);
lean_dec(v___x_839_);
v___x_841_ = 0;
lean_inc(v_constName_833_);
v___x_842_ = l_Lean_Environment_find_x3f(v_env_840_, v_constName_833_, v___x_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
return v___x_843_;
}
else
{
lean_object* v_val_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_constName_833_);
v_val_844_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_842_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_val_844_);
lean_dec(v___x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 0);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_val_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7___boxed(lean_object* v_constName_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_constName_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem(lean_object* v_declName_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; lean_object* v___f_866_; lean_object* v___x_867_; 
v___x_865_ = lean_box(1);
lean_inc(v_declName_859_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___boxed), 9, 2);
lean_closure_set(v___f_866_, 0, v___x_865_);
lean_closure_set(v___f_866_, 1, v_declName_859_);
v___x_867_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; uint8_t v___x_870_; lean_object* v___x_871_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = l_Lean_ConstantInfo_type(v_a_868_);
lean_dec(v_a_868_);
v___x_870_ = 0;
v___x_871_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_869_, v___f_866_, v___x_870_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
return v___x_871_;
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v___f_866_);
v_a_872_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_867_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_867_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___boxed(lean_object* v_declName_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_Meta_Grind_validateHomoTheorem(v_declName_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_886_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0(lean_object* v_00_u03b2_887_, lean_object* v_k_888_, lean_object* v_t_889_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v_k_888_, v_t_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___boxed(lean_object* v_00_u03b2_891_, lean_object* v_k_892_, lean_object* v_t_893_){
_start:
{
uint8_t v_res_894_; lean_object* v_r_895_; 
v_res_894_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0(v_00_u03b2_891_, v_k_892_, v_t_893_);
lean_dec(v_t_893_);
lean_dec(v_k_892_);
v_r_895_ = lean_box(v_res_894_);
return v_r_895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3(lean_object* v___y_896_, lean_object* v_as_897_, size_t v_sz_898_, size_t v_i_899_, lean_object* v_b_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_896_, v_as_897_, v_sz_898_, v_i_899_, v_b_900_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___boxed(lean_object* v___y_907_, lean_object* v_as_908_, lean_object* v_sz_909_, lean_object* v_i_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
size_t v_sz_boxed_917_; size_t v_i_boxed_918_; lean_object* v_res_919_; 
v_sz_boxed_917_ = lean_unbox_usize(v_sz_909_);
lean_dec(v_sz_909_);
v_i_boxed_918_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3(v___y_907_, v_as_908_, v_sz_boxed_917_, v_i_boxed_918_, v_b_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec_ref(v_as_908_);
lean_dec_ref(v___y_907_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4(lean_object* v_xs_920_, lean_object* v_inst_921_, lean_object* v_a_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_920_, v_a_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___boxed(lean_object* v_xs_929_, lean_object* v_inst_930_, lean_object* v_a_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4(v_xs_929_, v_inst_930_, v_a_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_xs_929_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5(lean_object* v_00_u03b1_938_, lean_object* v_msg_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___boxed(lean_object* v_00_u03b1_946_, lean_object* v_msg_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5(v_00_u03b1_946_, v_msg_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8(lean_object* v_00_u03b1_954_, lean_object* v_constName_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___boxed(lean_object* v_00_u03b1_962_, lean_object* v_constName_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8(v_00_u03b1_962_, v_constName_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_970_, lean_object* v_ref_971_, lean_object* v_constName_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_971_, v_constName_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_979_, lean_object* v_ref_980_, lean_object* v_constName_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10(v_00_u03b1_979_, v_ref_980_, v_constName_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v_ref_980_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11(lean_object* v_00_u03b1_988_, lean_object* v_ref_989_, lean_object* v_msg_990_, lean_object* v_declHint_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_989_, v_msg_990_, v_declHint_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___boxed(lean_object* v_00_u03b1_998_, lean_object* v_ref_999_, lean_object* v_msg_1000_, lean_object* v_declHint_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11(v_00_u03b1_998_, v_ref_999_, v_msg_1000_, v_declHint_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v_ref_999_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13(lean_object* v_msg_1008_, lean_object* v_declHint_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_1008_, v_declHint_1009_, v___y_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1016_, lean_object* v_declHint_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13(v_msg_1016_, v_declHint_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13(lean_object* v_00_u03b1_1024_, lean_object* v_ref_1025_, lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_1025_, v_msg_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1033_, lean_object* v_ref_1034_, lean_object* v_msg_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13(v_00_u03b1_1033_, v_ref_1034_, v_msg_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v_ref_1034_);
return v_res_1041_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__0));
v___x_1044_ = l_Lean_stringToMessageData(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__2));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__4));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0(lean_object* v_declName_1051_, lean_object* v_x_1052_, lean_object* v_concl_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___y_1063_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
lean_inc_ref(v_concl_1053_);
v___x_1089_ = l_Lean_Expr_cleanupAnnotations(v_concl_1053_);
v___x_1090_ = l_Lean_Expr_isApp(v___x_1089_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v___x_1089_);
v___y_1063_ = v_concl_1053_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1089_);
v___x_1092_ = l_Lean_Expr_isApp(v___x_1091_);
if (v___x_1092_ == 0)
{
lean_dec_ref(v___x_1091_);
v___y_1063_ = v_concl_1053_;
goto v___jp_1062_;
}
else
{
lean_object* v_arg_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_arg_1093_ = lean_ctor_get(v___x_1091_, 1);
lean_inc_ref(v_arg_1093_);
v___x_1094_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1091_);
v___x_1095_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3));
v___x_1096_ = l_Lean_Expr_isConstOf(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Lean_Expr_isApp(v___x_1094_);
if (v___x_1097_ == 0)
{
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_arg_1093_);
v___y_1063_ = v_concl_1053_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1094_);
v___x_1099_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_1100_ = l_Lean_Expr_isConstOf(v___x_1098_, v___x_1099_);
lean_dec_ref(v___x_1098_);
if (v___x_1100_ == 0)
{
lean_dec_ref(v_arg_1093_);
v___y_1063_ = v_concl_1053_;
goto v___jp_1062_;
}
else
{
lean_dec_ref(v_concl_1053_);
v___y_1063_ = v_arg_1093_;
goto v___jp_1062_;
}
}
}
else
{
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_concl_1053_);
v___y_1063_ = v_arg_1093_;
goto v___jp_1062_;
}
}
}
v___jp_1059_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
v___jp_1062_:
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = l_Lean_Expr_cleanupAnnotations(v___y_1063_);
v___x_1065_ = l_Lean_Expr_isApp(v___x_1064_);
if (v___x_1065_ == 0)
{
lean_dec_ref(v___x_1064_);
lean_dec(v_declName_1051_);
goto v___jp_1059_;
}
else
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1064_);
v___x_1067_ = l_Lean_Expr_isApp(v___x_1066_);
if (v___x_1067_ == 0)
{
lean_dec_ref(v___x_1066_);
lean_dec(v_declName_1051_);
goto v___jp_1059_;
}
else
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1066_);
v___x_1069_ = l_Lean_Expr_isApp(v___x_1068_);
if (v___x_1069_ == 0)
{
lean_dec_ref(v___x_1068_);
lean_dec(v_declName_1051_);
goto v___jp_1059_;
}
else
{
lean_object* v_arg_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v_arg_1070_ = lean_ctor_get(v___x_1068_, 1);
lean_inc_ref(v_arg_1070_);
v___x_1071_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1068_);
v___x_1072_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_1073_ = l_Lean_Expr_isConstOf(v___x_1071_, v___x_1072_);
lean_dec_ref(v___x_1071_);
if (v___x_1073_ == 0)
{
lean_dec_ref(v_arg_1070_);
lean_dec(v_declName_1051_);
goto v___jp_1059_;
}
else
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_Expr_getAppFn(v_arg_1070_);
if (lean_obj_tag(v___x_1074_) == 4)
{
lean_object* v_declName_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec_ref(v_arg_1070_);
lean_dec(v_declName_1051_);
v_declName_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_declName_1075_);
lean_dec_ref_known(v___x_1074_, 2);
v___x_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1076_, 0, v_declName_1075_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_dec_ref(v___x_1074_);
v___x_1078_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1);
v___x_1079_ = 0;
v___x_1080_ = l_Lean_MessageData_ofConstName(v_declName_1051_, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1078_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_indentExpr(v_arg_1070_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1087_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1088_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___boxed(lean_object* v_declName_1101_, lean_object* v_x_1102_, lean_object* v_concl_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0(v_declName_1101_, v_x_1102_, v_concl_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec_ref(v_x_1102_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(lean_object* v_declName_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___f_1116_; lean_object* v___x_1117_; 
lean_inc(v_declName_1110_);
v___f_1116_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1116_, 0, v_declName_1110_);
v___x_1117_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = l_Lean_ConstantInfo_type(v_a_1118_);
lean_dec(v_a_1118_);
v___x_1120_ = 0;
v___x_1121_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_1119_, v___f_1116_, v___x_1120_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1121_;
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v___f_1116_);
v_a_1122_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1117_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1117_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___boxed(lean_object* v_declName_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(v_declName_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
return v_res_1136_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0);
v___x_1142_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
lean_ctor_set(v___x_1142_, 2, v___x_1141_);
lean_ctor_set(v___x_1142_, 3, v___x_1141_);
lean_ctor_set(v___x_1142_, 4, v___x_1141_);
lean_ctor_set(v___x_1142_, 5, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(lean_object* v_ext_1143_, lean_object* v_b_1144_, uint8_t v_kind_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_toCold_1150_; lean_object* v_currNamespace_1151_; lean_object* v___x_1152_; lean_object* v_env_1153_; lean_object* v_nextMacroScope_1154_; lean_object* v_ngen_1155_; lean_object* v_auxDeclNGen_1156_; lean_object* v_traceState_1157_; lean_object* v_recordedDeps_1158_; lean_object* v_messages_1159_; lean_object* v_infoState_1160_; lean_object* v_snapshotTasks_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1188_; 
v_toCold_1150_ = lean_ctor_get(v___y_1147_, 0);
v_currNamespace_1151_ = lean_ctor_get(v_toCold_1150_, 4);
v___x_1152_ = lean_st_ref_take(v___y_1148_);
v_env_1153_ = lean_ctor_get(v___x_1152_, 0);
v_nextMacroScope_1154_ = lean_ctor_get(v___x_1152_, 1);
v_ngen_1155_ = lean_ctor_get(v___x_1152_, 2);
v_auxDeclNGen_1156_ = lean_ctor_get(v___x_1152_, 3);
v_traceState_1157_ = lean_ctor_get(v___x_1152_, 4);
v_recordedDeps_1158_ = lean_ctor_get(v___x_1152_, 6);
v_messages_1159_ = lean_ctor_get(v___x_1152_, 7);
v_infoState_1160_ = lean_ctor_get(v___x_1152_, 8);
v_snapshotTasks_1161_ = lean_ctor_get(v___x_1152_, 9);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v___x_1152_, 5);
lean_dec(v_unused_1189_);
v___x_1163_ = v___x_1152_;
v_isShared_1164_ = v_isSharedCheck_1188_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_snapshotTasks_1161_);
lean_inc(v_infoState_1160_);
lean_inc(v_messages_1159_);
lean_inc(v_recordedDeps_1158_);
lean_inc(v_traceState_1157_);
lean_inc(v_auxDeclNGen_1156_);
lean_inc(v_ngen_1155_);
lean_inc(v_nextMacroScope_1154_);
lean_inc(v_env_1153_);
lean_dec(v___x_1152_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1188_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_inc(v_currNamespace_1151_);
v___x_1165_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1153_, v_ext_1143_, v_b_1144_, v_kind_1145_, v_currNamespace_1151_);
v___x_1166_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 5, v___x_1166_);
lean_ctor_set(v___x_1163_, 0, v___x_1165_);
v___x_1168_ = v___x_1163_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_nextMacroScope_1154_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_ngen_1155_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_auxDeclNGen_1156_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v_traceState_1157_);
lean_ctor_set(v_reuseFailAlloc_1187_, 5, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1187_, 6, v_recordedDeps_1158_);
lean_ctor_set(v_reuseFailAlloc_1187_, 7, v_messages_1159_);
lean_ctor_set(v_reuseFailAlloc_1187_, 8, v_infoState_1160_);
lean_ctor_set(v_reuseFailAlloc_1187_, 9, v_snapshotTasks_1161_);
v___x_1168_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v_mctx_1171_; lean_object* v_zetaDeltaFVarIds_1172_; lean_object* v_postponed_1173_; lean_object* v_diag_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1185_; 
v___x_1169_ = lean_st_ref_put(v___y_1148_, v___x_1168_);
v___x_1170_ = lean_st_ref_take(v___y_1146_);
v_mctx_1171_ = lean_ctor_get(v___x_1170_, 0);
v_zetaDeltaFVarIds_1172_ = lean_ctor_get(v___x_1170_, 2);
v_postponed_1173_ = lean_ctor_get(v___x_1170_, 3);
v_diag_1174_ = lean_ctor_get(v___x_1170_, 4);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; 
v_unused_1186_ = lean_ctor_get(v___x_1170_, 1);
lean_dec(v_unused_1186_);
v___x_1176_ = v___x_1170_;
v_isShared_1177_ = v_isSharedCheck_1185_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_diag_1174_);
lean_inc(v_postponed_1173_);
lean_inc(v_zetaDeltaFVarIds_1172_);
lean_inc(v_mctx_1171_);
lean_dec(v___x_1170_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1185_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1179_);
v___x_1181_ = v___x_1176_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_mctx_1171_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_zetaDeltaFVarIds_1172_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_postponed_1173_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v_diag_1174_);
v___x_1181_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_st_ref_put(v___y_1146_, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1178_);
return v___x_1183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___boxed(lean_object* v_ext_1190_, lean_object* v_b_1191_, lean_object* v_kind_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
uint8_t v_kind_boxed_1197_; lean_object* v_res_1198_; 
v_kind_boxed_1197_ = lean_unbox(v_kind_1192_);
v_res_1198_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v_ext_1190_, v_b_1191_, v_kind_boxed_1197_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(lean_object* v_00_u03b1_1199_, lean_object* v_00_u03b2_1200_, lean_object* v_00_u03c3_1201_, lean_object* v_ext_1202_, lean_object* v_b_1203_, uint8_t v_kind_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v_ext_1202_, v_b_1203_, v_kind_1204_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___boxed(lean_object* v_00_u03b1_1211_, lean_object* v_00_u03b2_1212_, lean_object* v_00_u03c3_1213_, lean_object* v_ext_1214_, lean_object* v_b_1215_, lean_object* v_kind_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
uint8_t v_kind_boxed_1222_; lean_object* v_res_1223_; 
v_kind_boxed_1222_ = lean_unbox(v_kind_1216_);
v_res_1223_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(v_00_u03b1_1211_, v_00_u03b2_1212_, v_00_u03c3_1213_, v_ext_1214_, v_b_1215_, v_kind_boxed_1222_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0(uint8_t v_attrKind_1224_, lean_object* v_declName_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
lean_inc(v_declName_1225_);
v___x_1231_ = l_Lean_Meta_Grind_validateHomoTheorem(v_declName_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v___x_1232_; 
lean_dec_ref_known(v___x_1231_, 1);
v___x_1232_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(v_declName_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1244_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1244_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1244_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
if (lean_obj_tag(v_a_1233_) == 1)
{
lean_object* v_val_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_del_object(v___x_1235_);
v_val_1237_ = lean_ctor_get(v_a_1233_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v_a_1233_, 1);
v___x_1238_ = l_Lean_Meta_Grind_homoSourceTypesExt;
v___x_1239_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v___x_1238_, v_val_1237_, v_attrKind_1224_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_dec(v_a_1233_);
v___x_1240_ = lean_box(0);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1240_);
v___x_1242_ = v___x_1235_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_a_1245_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1232_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1232_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
else
{
lean_dec(v_declName_1225_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed(lean_object* v_attrKind_1253_, lean_object* v_declName_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
uint8_t v_attrKind_boxed_1260_; lean_object* v_res_1261_; 
v_attrKind_boxed_1260_ = lean_unbox(v_attrKind_1253_);
v_res_1261_ = l_Lean_Meta_Grind_addHomoAttr___lam__0(v_attrKind_boxed_1260_, v_declName_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object* v_declName_1262_, uint8_t v_attrKind_1263_, uint8_t v_fallback_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v___x_1270_; lean_object* v_validate_1271_; 
v___x_1270_ = lean_box(v_attrKind_1263_);
v_validate_1271_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed), 7, 1);
lean_closure_set(v_validate_1271_, 0, v___x_1270_);
if (v_fallback_1264_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = l_Lean_Meta_Grind_homoExt;
v___x_1273_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v___x_1272_, v_declName_1262_, v_attrKind_1263_, v_validate_1271_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1273_;
}
else
{
lean_object* v___x_1274_; 
lean_dec_ref(v_validate_1271_);
lean_inc(v_declName_1262_);
v___x_1274_ = l_Lean_Meta_Grind_addHomoAttr___lam__0(v_attrKind_1263_, v_declName_1262_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; 
lean_dec_ref_known(v___x_1274_, 1);
v___x_1275_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_1262_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v_expr_1277_; lean_object* v_pattern_1278_; lean_object* v_rhs_1279_; uint8_t v_perm_1280_; lean_object* v_rhsVarMask_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1290_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1275_, 1);
v_expr_1277_ = lean_ctor_get(v_a_1276_, 0);
v_pattern_1278_ = lean_ctor_get(v_a_1276_, 1);
v_rhs_1279_ = lean_ctor_get(v_a_1276_, 2);
v_perm_1280_ = lean_ctor_get_uint8(v_a_1276_, sizeof(void*)*4);
v_rhsVarMask_1281_ = lean_ctor_get(v_a_1276_, 3);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_a_1276_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1283_ = v_a_1276_;
v_isShared_1284_ = v_isSharedCheck_1290_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_rhsVarMask_1281_);
lean_inc(v_rhs_1279_);
lean_inc(v_pattern_1278_);
lean_inc(v_expr_1277_);
lean_dec(v_a_1276_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1290_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = l_Lean_Meta_Grind_homoExt;
if (v_isShared_1284_ == 0)
{
v___x_1287_ = v___x_1283_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_expr_1277_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_pattern_1278_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_rhs_1279_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_rhsVarMask_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1289_, sizeof(void*)*4, v_perm_1280_);
v___x_1287_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; 
lean_ctor_set_uint8(v___x_1287_, sizeof(void*)*4 + 1, v_fallback_1264_);
v___x_1288_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v___x_1285_, v___x_1287_, v_attrKind_1263_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1288_;
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1275_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1275_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_dec(v_declName_1262_);
return v___x_1274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___boxed(lean_object* v_declName_1299_, lean_object* v_attrKind_1300_, lean_object* v_fallback_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
uint8_t v_attrKind_boxed_1307_; uint8_t v_fallback_boxed_1308_; lean_object* v_res_1309_; 
v_attrKind_boxed_1307_ = lean_unbox(v_attrKind_1300_);
v_fallback_boxed_1308_ = lean_unbox(v_fallback_1301_);
v_res_1309_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_1299_, v_attrKind_boxed_1307_, v_fallback_boxed_1308_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
return v_res_1309_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(lean_object* v_x_1315_, lean_object* v_x_1316_){
_start:
{
lean_object* v_declName_1317_; lean_object* v_arity_1318_; lean_object* v_declName_1319_; lean_object* v_arity_1320_; uint8_t v___x_1321_; 
v_declName_1317_ = lean_ctor_get(v_x_1315_, 0);
v_arity_1318_ = lean_ctor_get(v_x_1315_, 1);
v_declName_1319_ = lean_ctor_get(v_x_1316_, 0);
v_arity_1320_ = lean_ctor_get(v_x_1316_, 1);
v___x_1321_ = lean_name_eq(v_declName_1317_, v_declName_1319_);
if (v___x_1321_ == 0)
{
return v___x_1321_;
}
else
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_nat_dec_eq(v_arity_1318_, v_arity_1320_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq___boxed(lean_object* v_x_1323_, lean_object* v_x_1324_){
_start:
{
uint8_t v_res_1325_; lean_object* v_r_1326_; 
v_res_1325_ = l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(v_x_1323_, v_x_1324_);
lean_dec_ref(v_x_1324_);
lean_dec_ref(v_x_1323_);
v_r_1326_ = lean_box(v_res_1325_);
return v_r_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object* v_s_1329_, lean_object* v_x_1330_){
_start:
{
lean_object* v_fst_1331_; lean_object* v_snd_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1345_; 
v_fst_1331_ = lean_ctor_get(v_x_1330_, 0);
v_snd_1332_ = lean_ctor_get(v_x_1330_, 1);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_x_1330_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1334_ = v_x_1330_;
v_isShared_1335_ = v_isSharedCheck_1345_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_snd_1332_);
lean_inc(v_fst_1331_);
lean_dec(v_x_1330_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1345_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___y_1337_; lean_object* v___x_1342_; 
v___x_1342_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_s_1329_, v_fst_1331_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_box(0);
v___y_1337_ = v___x_1343_;
goto v___jp_1336_;
}
else
{
lean_object* v_val_1344_; 
v_val_1344_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v___x_1342_, 1);
v___y_1337_ = v_val_1344_;
goto v___jp_1336_;
}
v___jp_1336_:
{
lean_object* v___x_1339_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set_tag(v___x_1334_, 1);
lean_ctor_set(v___x_1334_, 1, v___y_1337_);
lean_ctor_set(v___x_1334_, 0, v_snd_1332_);
v___x_1339_ = v___x_1334_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_snd_1332_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___y_1337_);
v___x_1339_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1331_, v___x_1339_, v_s_1329_);
return v___x_1340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object* v_x_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1348_, 0, v_a_1347_);
lean_inc_ref_n(v___x_1348_, 2);
v___x_1349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
lean_ctor_set(v___x_1349_, 2, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object* v_x_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(v_x_1350_, v_a_1351_);
lean_dec_ref(v_x_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_));
v___x_1371_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object* v_a_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_();
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg(lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_env_1378_; lean_object* v___x_1379_; lean_object* v_ext_1380_; lean_object* v_toEnvExtension_1381_; lean_object* v_asyncMode_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1376_ = lean_box(1);
v___x_1377_ = lean_st_ref_get(v_a_1374_);
v_env_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc_ref(v_env_1378_);
lean_dec(v___x_1377_);
v___x_1379_ = l_Lean_Meta_Grind_homoPredExt;
v_ext_1380_ = lean_ctor_get(v___x_1379_, 1);
v_toEnvExtension_1381_ = lean_ctor_get(v_ext_1380_, 0);
v_asyncMode_1382_ = lean_ctor_get(v_toEnvExtension_1381_, 2);
v___x_1383_ = 0;
v___x_1384_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1376_, v___x_1379_, v_env_1378_, v_asyncMode_1382_, v___x_1383_);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg___boxed(lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1386_);
lean_dec(v_a_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems(lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___boxed(lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Meta_Grind_getHomoPredTheorems(v_a_1393_, v_a_1394_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___f_1404_; lean_object* v___x_2163__overap_1405_; lean_object* v___x_1406_; 
v___f_1404_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___closed__0));
v___x_2163__overap_1405_ = lean_panic_fn_borrowed(v___f_1404_, v_msg_1398_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
v___x_1406_ = lean_apply_5(v___x_2163__overap_1405_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, lean_box(0));
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___boxed(lean_object* v_msg_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(v_msg_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
return v_res_1413_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(lean_object* v_xs_1414_, lean_object* v_ys_1415_, lean_object* v_x_1416_){
_start:
{
lean_object* v_zero_1417_; uint8_t v_isZero_1418_; 
v_zero_1417_ = lean_unsigned_to_nat(0u);
v_isZero_1418_ = lean_nat_dec_eq(v_x_1416_, v_zero_1417_);
if (v_isZero_1418_ == 1)
{
lean_dec(v_x_1416_);
return v_isZero_1418_;
}
else
{
lean_object* v_one_1419_; lean_object* v_n_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v_one_1419_ = lean_unsigned_to_nat(1u);
v_n_1420_ = lean_nat_sub(v_x_1416_, v_one_1419_);
lean_dec(v_x_1416_);
v___x_1421_ = lean_array_fget_borrowed(v_xs_1414_, v_n_1420_);
v___x_1422_ = lean_array_fget_borrowed(v_ys_1415_, v_n_1420_);
v___x_1423_ = lean_expr_eqv(v___x_1421_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_dec(v_n_1420_);
return v___x_1423_;
}
else
{
v_x_1416_ = v_n_1420_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg___boxed(lean_object* v_xs_1425_, lean_object* v_ys_1426_, lean_object* v_x_1427_){
_start:
{
uint8_t v_res_1428_; lean_object* v_r_1429_; 
v_res_1428_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v_xs_1425_, v_ys_1426_, v_x_1427_);
lean_dec_ref(v_ys_1426_);
lean_dec_ref(v_xs_1425_);
v_r_1429_ = lean_box(v_res_1428_);
return v_r_1429_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1430_; lean_object* v_dummy_1431_; 
v___x_1430_ = lean_box(0);
v_dummy_1431_ = l_Lean_Expr_sort___override(v___x_1430_);
return v_dummy_1431_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_addHomoPredAttr___lam__0(lean_object* v_a_1432_, lean_object* v_e_1433_){
_start:
{
uint8_t v___y_1435_; uint8_t v___x_1451_; 
v___x_1451_ = l_Lean_Expr_isApp(v_e_1433_);
if (v___x_1451_ == 0)
{
v___y_1435_ = v___x_1451_;
goto v___jp_1434_;
}
else
{
lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = l_Lean_Expr_getAppFn(v_e_1433_);
v___x_1453_ = l_Lean_Expr_isConst(v___x_1452_);
lean_dec_ref(v___x_1452_);
v___y_1435_ = v___x_1453_;
goto v___jp_1434_;
}
v___jp_1434_:
{
if (v___y_1435_ == 0)
{
lean_dec_ref(v_e_1433_);
return v___y_1435_;
}
else
{
lean_object* v_dummy_1436_; lean_object* v_nargs_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_dummy_1436_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0, &l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0);
v_nargs_1437_ = l_Lean_Expr_getAppNumArgs(v_e_1433_);
lean_inc(v_nargs_1437_);
v___x_1438_ = lean_mk_array(v_nargs_1437_, v_dummy_1436_);
v___x_1439_ = lean_unsigned_to_nat(1u);
v___x_1440_ = lean_nat_sub(v_nargs_1437_, v___x_1439_);
lean_dec(v_nargs_1437_);
v___x_1441_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1433_, v___x_1438_, v___x_1440_);
v___x_1442_ = lean_array_get_size(v___x_1441_);
v___x_1443_ = lean_array_get_size(v_a_1432_);
v___x_1444_ = lean_nat_dec_lt(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1445_ = lean_nat_sub(v___x_1442_, v___x_1443_);
v___x_1446_ = l_Array_extract___redArg(v___x_1441_, v___x_1445_, v___x_1442_);
lean_dec_ref(v___x_1441_);
v___x_1447_ = lean_array_get_size(v___x_1446_);
v___x_1448_ = lean_nat_dec_eq(v___x_1447_, v___x_1443_);
if (v___x_1448_ == 0)
{
lean_dec_ref(v___x_1446_);
return v___x_1448_;
}
else
{
uint8_t v___x_1449_; 
v___x_1449_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v___x_1446_, v_a_1432_, v___x_1447_);
lean_dec_ref(v___x_1446_);
return v___x_1449_;
}
}
else
{
uint8_t v___x_1450_; 
lean_dec_ref(v___x_1441_);
v___x_1450_ = 0;
return v___x_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__0___boxed(lean_object* v_a_1454_, lean_object* v_e_1455_){
_start:
{
uint8_t v_res_1456_; lean_object* v_r_1457_; 
v_res_1456_ = l_Lean_Meta_Grind_addHomoPredAttr___lam__0(v_a_1454_, v_e_1455_);
lean_dec_ref(v_a_1454_);
v_r_1457_ = lean_box(v_res_1456_);
return v_r_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(lean_object* v_as_1458_, size_t v_i_1459_, size_t v_stop_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_a_1467_; uint8_t v___x_1471_; 
v___x_1471_ = lean_usize_dec_eq(v_i_1459_, v_stop_1460_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_array_uget_borrowed(v_as_1458_, v_i_1459_);
v___x_1473_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_1472_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; uint8_t v___x_1475_; uint8_t v___x_1476_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v___x_1475_ = l_Lean_LocalDecl_binderInfo(v_a_1474_);
lean_dec(v_a_1474_);
v___x_1476_ = l_Lean_BinderInfo_isExplicit(v___x_1475_);
if (v___x_1476_ == 0)
{
v_a_1467_ = v_b_1461_;
goto v___jp_1466_;
}
else
{
lean_object* v___x_1477_; 
lean_inc(v___x_1472_);
v___x_1477_ = lean_array_push(v_b_1461_, v___x_1472_);
v_a_1467_ = v___x_1477_;
goto v___jp_1466_;
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v_b_1461_);
v_a_1478_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1473_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1473_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_b_1461_);
return v___x_1486_;
}
v___jp_1466_:
{
size_t v___x_1468_; size_t v___x_1469_; 
v___x_1468_ = ((size_t)1ULL);
v___x_1469_ = lean_usize_add(v_i_1459_, v___x_1468_);
v_i_1459_ = v___x_1469_;
v_b_1461_ = v_a_1467_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg___boxed(lean_object* v_as_1487_, lean_object* v_i_1488_, lean_object* v_stop_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
size_t v_i_boxed_1495_; size_t v_stop_boxed_1496_; lean_object* v_res_1497_; 
v_i_boxed_1495_ = lean_unbox_usize(v_i_1488_);
lean_dec(v_i_1488_);
v_stop_boxed_1496_ = lean_unbox_usize(v_stop_1489_);
lean_dec(v_stop_1489_);
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_as_1487_, v_i_boxed_1495_, v_stop_boxed_1496_, v_b_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec_ref(v_as_1487_);
return v_res_1497_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1501_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__2));
v___x_1502_ = lean_unsigned_to_nat(41u);
v___x_1503_ = lean_unsigned_to_nat(169u);
v___x_1504_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__1));
v___x_1505_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__0));
v___x_1506_ = l_mkPanicMessageWithDecl(v___x_1505_, v___x_1504_, v___x_1503_, v___x_1502_, v___x_1501_);
return v___x_1506_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__4));
v___x_1509_ = l_Lean_stringToMessageData(v___x_1508_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__6));
v___x_1512_ = l_Lean_stringToMessageData(v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__8));
v___x_1515_ = l_Lean_stringToMessageData(v___x_1514_);
return v___x_1515_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__10));
v___x_1518_ = l_Lean_stringToMessageData(v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1(lean_object* v_declName_1521_, uint8_t v_attrKind_1522_, lean_object* v_xs_1523_, lean_object* v_type_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v_a_1552_; lean_object* v___y_1565_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = lean_array_get_size(v_xs_1523_);
v___x_1577_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__12));
v___x_1578_ = lean_nat_dec_lt(v___x_1575_, v___x_1576_);
if (v___x_1578_ == 0)
{
v_a_1552_ = v___x_1577_;
goto v___jp_1551_;
}
else
{
uint8_t v___x_1579_; 
v___x_1579_ = lean_nat_dec_le(v___x_1576_, v___x_1576_);
if (v___x_1579_ == 0)
{
if (v___x_1578_ == 0)
{
v_a_1552_ = v___x_1577_;
goto v___jp_1551_;
}
else
{
size_t v___x_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = lean_usize_of_nat(v___x_1576_);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_xs_1523_, v___x_1580_, v___x_1581_, v___x_1577_, v___y_1525_, v___y_1527_, v___y_1528_);
v___y_1565_ = v___x_1582_;
goto v___jp_1564_;
}
}
else
{
size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = ((size_t)0ULL);
v___x_1584_ = lean_usize_of_nat(v___x_1576_);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_xs_1523_, v___x_1583_, v___x_1584_, v___x_1577_, v___y_1525_, v___y_1527_, v___y_1528_);
v___y_1565_ = v___x_1585_;
goto v___jp_1564_;
}
}
v___jp_1530_:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_find_expr(v___y_1532_, v_type_1524_);
lean_dec_ref(v___y_1532_);
if (lean_obj_tag(v___x_1533_) == 1)
{
lean_object* v_val_1534_; lean_object* v___x_1535_; 
v_val_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = l_Lean_Expr_getAppFn(v_val_1534_);
lean_dec(v_val_1534_);
if (lean_obj_tag(v___x_1535_) == 4)
{
lean_object* v_declName_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_declName_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_declName_1536_);
lean_dec_ref_known(v___x_1535_, 2);
v___x_1537_ = l_Lean_Meta_Grind_homoPredExt;
v___x_1538_ = lean_array_get_size(v___y_1531_);
lean_dec_ref(v___y_1531_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_declName_1521_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_declName_1536_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v___x_1537_, v___x_1540_, v_attrKind_1522_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1541_;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec_ref(v___x_1535_);
lean_dec_ref(v___y_1531_);
lean_dec(v_declName_1521_);
v___x_1542_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3);
v___x_1543_ = l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(v___x_1542_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1543_;
}
}
else
{
lean_object* v___x_1544_; uint8_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec(v___x_1533_);
lean_dec_ref(v___y_1531_);
v___x_1544_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5);
v___x_1545_ = 0;
v___x_1546_ = l_Lean_MessageData_ofConstName(v_declName_1521_, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1544_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1549_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1550_;
}
}
v___jp_1551_:
{
lean_object* v___f_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
lean_inc_ref(v_a_1552_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1553_, 0, v_a_1552_);
v___x_1554_ = lean_array_get_size(v_a_1552_);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_nat_dec_eq(v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
v___y_1531_ = v_a_1552_;
v___y_1532_ = v___f_1553_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec_ref(v___f_1553_);
lean_dec_ref(v_a_1552_);
v___x_1557_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9);
v___x_1558_ = 0;
v___x_1559_ = l_Lean_MessageData_ofConstName(v_declName_1521_, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1557_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1562_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1563_;
}
}
v___jp_1564_:
{
if (lean_obj_tag(v___y_1565_) == 0)
{
lean_object* v_a_1566_; 
v_a_1566_ = lean_ctor_get(v___y_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___y_1565_, 1);
v_a_1552_ = v_a_1566_;
goto v___jp_1551_;
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_declName_1521_);
v_a_1567_ = lean_ctor_get(v___y_1565_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___y_1565_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___y_1565_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___y_1565_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___boxed(lean_object* v_declName_1586_, lean_object* v_attrKind_1587_, lean_object* v_xs_1588_, lean_object* v_type_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
uint8_t v_attrKind_boxed_1595_; lean_object* v_res_1596_; 
v_attrKind_boxed_1595_ = lean_unbox(v_attrKind_1587_);
v_res_1596_ = l_Lean_Meta_Grind_addHomoPredAttr___lam__1(v_declName_1586_, v_attrKind_boxed_1595_, v_xs_1588_, v_type_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec_ref(v_type_1589_);
lean_dec_ref(v_xs_1588_);
return v_res_1596_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___closed__1(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___closed__0));
v___x_1599_ = l_Lean_stringToMessageData(v___x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object* v_declName_1600_, uint8_t v_attrKind_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v___f_1608_; lean_object* v___x_1609_; 
v___x_1607_ = lean_box(v_attrKind_1601_);
lean_inc_n(v_declName_1600_, 2);
v___f_1608_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1608_, 0, v_declName_1600_);
lean_closure_set(v___f_1608_, 1, v___x_1607_);
v___x_1609_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_1600_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___x_1619_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = l_Lean_ConstantInfo_type(v_a_1610_);
lean_dec(v_a_1610_);
lean_inc_ref(v___x_1611_);
v___x_1619_ = l_Lean_Meta_isProp(v___x_1611_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; uint8_t v___x_1621_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = lean_unbox(v_a_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_dec_ref(v___x_1611_);
lean_dec_ref(v___f_1608_);
v___x_1622_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9);
v___x_1623_ = lean_unbox(v_a_1620_);
lean_dec(v_a_1620_);
v___x_1624_ = l_Lean_MessageData_ofConstName(v_declName_1600_, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1622_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___closed__1, &l_Lean_Meta_Grind_addHomoPredAttr___closed__1_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___closed__1);
v___x_1627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1627_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
return v___x_1628_;
}
else
{
lean_dec(v_a_1620_);
lean_dec(v_declName_1600_);
v___y_1613_ = v_a_1602_;
v___y_1614_ = v_a_1603_;
v___y_1615_ = v_a_1604_;
v___y_1616_ = v_a_1605_;
goto v___jp_1612_;
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v___x_1611_);
lean_dec_ref(v___f_1608_);
lean_dec(v_declName_1600_);
v_a_1629_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1619_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1619_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
v___jp_1612_:
{
uint8_t v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = 0;
v___x_1618_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_1611_, v___f_1608_, v___x_1617_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
return v___x_1618_;
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v___f_1608_);
lean_dec(v_declName_1600_);
v_a_1637_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1609_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1609_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
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
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___boxed(lean_object* v_declName_1645_, lean_object* v_attrKind_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
uint8_t v_attrKind_boxed_1652_; lean_object* v_res_1653_; 
v_attrKind_boxed_1652_ = lean_unbox(v_attrKind_1646_);
v_res_1653_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_1645_, v_attrKind_boxed_1652_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
return v_res_1653_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0(lean_object* v_xs_1654_, lean_object* v_ys_1655_, lean_object* v_hsz_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
uint8_t v___x_1659_; 
v___x_1659_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v_xs_1654_, v_ys_1655_, v_x_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___boxed(lean_object* v_xs_1660_, lean_object* v_ys_1661_, lean_object* v_hsz_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_){
_start:
{
uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_res_1665_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0(v_xs_1660_, v_ys_1661_, v_hsz_1662_, v_x_1663_, v_x_1664_);
lean_dec_ref(v_ys_1661_);
lean_dec_ref(v_xs_1660_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2(lean_object* v_as_1667_, size_t v_i_1668_, size_t v_stop_1669_, lean_object* v_b_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_as_1667_, v_i_1668_, v_stop_1669_, v_b_1670_, v___y_1671_, v___y_1673_, v___y_1674_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___boxed(lean_object* v_as_1677_, lean_object* v_i_1678_, lean_object* v_stop_1679_, lean_object* v_b_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
size_t v_i_boxed_1686_; size_t v_stop_boxed_1687_; lean_object* v_res_1688_; 
v_i_boxed_1686_ = lean_unbox_usize(v_i_1678_);
lean_dec(v_i_1678_);
v_stop_boxed_1687_ = lean_unbox_usize(v_stop_1679_);
lean_dec(v_stop_1679_);
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2(v_as_1677_, v_i_boxed_1686_, v_stop_boxed_1687_, v_b_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v_as_1677_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(lean_object* v___x_1689_, lean_object* v_as_x27_1690_, lean_object* v_b_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
if (lean_obj_tag(v_as_x27_1690_) == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v_b_1691_);
return v___x_1697_;
}
else
{
lean_object* v_head_1698_; lean_object* v_tail_1699_; lean_object* v___y_1701_; uint8_t v___y_1702_; lean_object* v_a_1706_; lean_object* v_declName_1709_; lean_object* v_arity_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_head_1698_ = lean_ctor_get(v_as_x27_1690_, 0);
v_tail_1699_ = lean_ctor_get(v_as_x27_1690_, 1);
v_declName_1709_ = lean_ctor_get(v_head_1698_, 0);
v_arity_1710_ = lean_ctor_get(v_head_1698_, 1);
v___x_1711_ = lean_array_get_size(v___x_1689_);
v___x_1712_ = lean_nat_dec_le(v_arity_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
v_as_x27_1690_ = v_tail_1699_;
goto _start;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = lean_nat_sub(v___x_1711_, v_arity_1710_);
v___x_1715_ = l_Array_extract___redArg(v___x_1689_, v___x_1714_, v___x_1711_);
lean_inc(v_declName_1709_);
v___x_1716_ = l_Lean_Meta_mkAppM(v_declName_1709_, v___x_1715_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc_n(v_a_1717_, 2);
lean_dec_ref_known(v___x_1716_, 1);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
lean_inc(v___y_1693_);
lean_inc_ref(v___y_1692_);
v___x_1718_ = lean_infer_type(v_a_1717_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_a_1717_);
lean_ctor_set(v___x_1720_, 1, v_a_1719_);
v___x_1721_ = lean_array_push(v_b_1691_, v___x_1720_);
v_as_x27_1690_ = v_tail_1699_;
v_b_1691_ = v___x_1721_;
goto _start;
}
else
{
lean_object* v_a_1723_; 
lean_dec(v_a_1717_);
v_a_1723_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1718_, 1);
v_a_1706_ = v_a_1723_;
goto v___jp_1705_;
}
}
else
{
lean_object* v_a_1724_; 
v_a_1724_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1716_, 1);
v_a_1706_ = v_a_1724_;
goto v___jp_1705_;
}
}
v___jp_1700_:
{
if (v___y_1702_ == 0)
{
lean_dec_ref(v___y_1701_);
v_as_x27_1690_ = v_tail_1699_;
goto _start;
}
else
{
lean_object* v___x_1704_; 
lean_dec_ref(v_b_1691_);
v___x_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___y_1701_);
return v___x_1704_;
}
}
v___jp_1705_:
{
uint8_t v___x_1707_; 
v___x_1707_ = l_Lean_Exception_isInterrupt(v_a_1706_);
if (v___x_1707_ == 0)
{
uint8_t v___x_1708_; 
lean_inc_ref(v_a_1706_);
v___x_1708_ = l_Lean_Exception_isRuntime(v_a_1706_);
v___y_1701_ = v_a_1706_;
v___y_1702_ = v___x_1708_;
goto v___jp_1700_;
}
else
{
v___y_1701_ = v_a_1706_;
v___y_1702_ = v___x_1707_;
goto v___jp_1700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg___boxed(lean_object* v___x_1725_, lean_object* v_as_x27_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1725_, v_as_x27_1726_, v_b_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v_as_x27_1726_);
lean_dec_ref(v___x_1725_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHomoPredInstances(lean_object* v_e_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Expr_getAppFn(v_e_1736_);
if (lean_obj_tag(v___x_1742_) == 4)
{
lean_object* v_declName_1743_; lean_object* v___x_1744_; lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1763_; 
v_declName_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_declName_1743_);
lean_dec_ref_known(v___x_1742_, 2);
v___x_1744_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1740_);
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1763_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1763_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1745_, v_declName_1743_);
lean_dec(v_declName_1743_);
lean_dec(v_a_1745_);
if (lean_obj_tag(v___x_1749_) == 1)
{
lean_object* v_val_1750_; lean_object* v_dummy_1751_; lean_object* v_nargs_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_del_object(v___x_1747_);
v_val_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_val_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v_dummy_1751_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0, &l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0);
v_nargs_1752_ = l_Lean_Expr_getAppNumArgs(v_e_1736_);
lean_inc(v_nargs_1752_);
v___x_1753_ = lean_mk_array(v_nargs_1752_, v_dummy_1751_);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = lean_nat_sub(v_nargs_1752_, v___x_1754_);
lean_dec(v_nargs_1752_);
v___x_1756_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1736_, v___x_1753_, v___x_1755_);
v___x_1757_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
v___x_1758_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1756_, v_val_1750_, v___x_1757_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
lean_dec(v_val_1750_);
lean_dec_ref(v___x_1756_);
return v___x_1758_;
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
lean_dec(v___x_1749_);
lean_dec_ref(v_e_1736_);
v___x_1759_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1759_);
v___x_1761_ = v___x_1747_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
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
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec_ref(v___x_1742_);
lean_dec_ref(v_e_1736_);
v___x_1764_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHomoPredInstances___boxed(lean_object* v_e_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Meta_Grind_mkHomoPredInstances(v_e_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0(lean_object* v___x_1773_, lean_object* v_as_1774_, lean_object* v_as_x27_1775_, lean_object* v_b_1776_, lean_object* v_a_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1773_, v_as_x27_1775_, v_b_1776_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___boxed(lean_object* v___x_1784_, lean_object* v_as_1785_, lean_object* v_as_x27_1786_, lean_object* v_b_1787_, lean_object* v_a_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0(v___x_1784_, v_as_1785_, v_as_x27_1786_, v_b_1787_, v_a_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v_as_x27_1786_);
lean_dec(v_as_1785_);
lean_dec_ref(v___x_1784_);
return v_res_1794_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_homoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_homoExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_homoSourceTypesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_homoSourceTypesExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_homoPredExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_homoPredExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
}
#ifdef __cplusplus
}
#endif
