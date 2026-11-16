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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
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
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpExt(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "homoSourceTypesExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 10, 151, 10, 152, 93, 193, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_;
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedHomoPredTheorem = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedHomoPredTheorem_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem = (const lean_object*)&l_Lean_Meta_Grind_instBEqHomoPredTheorem___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "homoPredExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2438845489____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 129, 210, 121, 39, 93, 224, 42)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_addImportedGlobals___boxed, .m_arity = 9, .m_num_fixed = 6, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2__value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object* v___y_30_){
_start:
{
lean_inc(v___y_30_);
return v___y_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(v___y_31_);
lean_dec(v___y_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object* v_x_33_, lean_object* v_a_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v_a_34_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v_x_38_, lean_object* v_a_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(v_x_38_, v_a_39_, v___y_40_);
lean_dec_ref(v___y_40_);
lean_dec(v_x_38_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object* v_x_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_45_, 0, v_a_44_);
lean_inc_ref_n(v___x_45_, 2);
v___x_46_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
lean_ctor_set(v___x_46_, 2, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v_x_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(v_x_47_, v_a_48_);
lean_dec_ref(v_x_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(lean_object* v___x_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v___x_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(v___x_53_);
return v_res_55_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_66_; lean_object* v___f_67_; 
v___x_66_ = l_Lean_NameSet_empty;
v___f_67_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_67_, 0, v___x_66_);
return v___f_67_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___f_70_; lean_object* v___x_71_; 
v___f_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___f_69_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___f_70_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_);
v___x_71_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedGlobals___boxed), 9, 6);
lean_closure_set(v___x_71_, 0, lean_box(0));
lean_closure_set(v___x_71_, 1, lean_box(0));
lean_closure_set(v___x_71_, 2, lean_box(0));
lean_closure_set(v___x_71_, 3, v___f_70_);
lean_closure_set(v___x_71_, 4, v___f_69_);
lean_closure_set(v___x_71_, 5, v___f_68_);
return v___x_71_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___f_75_; lean_object* v___f_76_; lean_object* v___x_77_; lean_object* v___f_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_72_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_);
v___x_73_ = lean_box(0);
v___x_74_ = 0;
v___f_75_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___f_76_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_77_ = l_Lean_NameSet_empty;
v___f_78_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_79_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_));
v___x_80_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___f_78_);
lean_ctor_set(v___x_80_, 2, v___f_78_);
lean_ctor_set(v___x_80_, 3, v___x_77_);
lean_ctor_set(v___x_80_, 4, v___f_76_);
lean_ctor_set(v___x_80_, 5, v___f_75_);
lean_ctor_set(v___x_80_, 6, v___x_73_);
lean_ctor_set(v___x_80_, 7, v___x_72_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*8, v___x_74_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*8 + 1, v___x_74_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_);
v___x_83_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2____boxed(lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_1405043254____hygCtx___hyg_2_();
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg(lean_object* v_a_86_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_env_90_; lean_object* v___x_91_; lean_object* v_ext_92_; lean_object* v_toEnvExtension_93_; lean_object* v_asyncMode_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_88_ = lean_box(1);
v___x_89_ = lean_st_ref_get(v_a_86_);
v_env_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc_ref(v_env_90_);
lean_dec(v___x_89_);
v___x_91_ = l_Lean_Meta_Grind_homoSourceTypesExt;
v_ext_92_ = lean_ctor_get(v___x_91_, 1);
v_toEnvExtension_93_ = lean_ctor_get(v_ext_92_, 0);
v_asyncMode_94_ = lean_ctor_get(v_toEnvExtension_93_, 2);
v___x_95_ = 0;
v___x_96_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_88_, v___x_91_, v_env_90_, v_asyncMode_94_, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg___boxed(lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_98_);
lean_dec(v_a_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes(lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___boxed(lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Meta_Grind_getHomoSourceTypes(v_a_105_, v_a_106_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0(lean_object* v_k_109_, lean_object* v_b_110_, lean_object* v_c_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; 
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
lean_inc(v___y_113_);
lean_inc_ref(v___y_112_);
v___x_117_ = lean_apply_7(v_k_109_, v_b_110_, v_c_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, lean_box(0));
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0___boxed(lean_object* v_k_118_, lean_object* v_b_119_, lean_object* v_c_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0(v_k_118_, v_b_119_, v_c_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(lean_object* v_type_127_, lean_object* v_k_128_, uint8_t v_cleanupAnnotations_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___f_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___f_135_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_135_, 0, v_k_128_);
v___x_136_ = 0;
v___x_137_ = lean_box(0);
v___x_138_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_136_, v___x_137_, v_type_127_, v___f_135_, v_cleanupAnnotations_129_, v___x_136_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
v_a_147_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_138_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_138_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg___boxed(lean_object* v_type_155_, lean_object* v_k_156_, lean_object* v_cleanupAnnotations_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_163_; lean_object* v_res_164_; 
v_cleanupAnnotations_boxed_163_ = lean_unbox(v_cleanupAnnotations_157_);
v_res_164_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v_type_155_, v_k_156_, v_cleanupAnnotations_boxed_163_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8(lean_object* v_00_u03b1_165_, lean_object* v_type_166_, lean_object* v_k_167_, uint8_t v_cleanupAnnotations_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v_type_166_, v_k_167_, v_cleanupAnnotations_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___boxed(lean_object* v_00_u03b1_175_, lean_object* v_type_176_, lean_object* v_k_177_, lean_object* v_cleanupAnnotations_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_184_; lean_object* v_res_185_; 
v_cleanupAnnotations_boxed_184_ = lean_unbox(v_cleanupAnnotations_178_);
v_res_185_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8(v_00_u03b1_175_, v_type_176_, v_k_177_, v_cleanupAnnotations_boxed_184_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_185_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(lean_object* v_k_186_, lean_object* v_t_187_){
_start:
{
if (lean_obj_tag(v_t_187_) == 0)
{
lean_object* v_k_188_; lean_object* v_l_189_; lean_object* v_r_190_; uint8_t v___x_191_; 
v_k_188_ = lean_ctor_get(v_t_187_, 1);
v_l_189_ = lean_ctor_get(v_t_187_, 3);
v_r_190_ = lean_ctor_get(v_t_187_, 4);
v___x_191_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_186_, v_k_188_);
switch(v___x_191_)
{
case 0:
{
v_t_187_ = v_l_189_;
goto _start;
}
case 1:
{
uint8_t v___x_193_; 
v___x_193_ = 1;
return v___x_193_;
}
default: 
{
v_t_187_ = v_r_190_;
goto _start;
}
}
}
else
{
uint8_t v___x_195_; 
v___x_195_ = 0;
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg___boxed(lean_object* v_k_196_, lean_object* v_t_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v_k_196_, v_t_197_);
lean_dec(v_t_197_);
lean_dec(v_k_196_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(lean_object* v_msgData_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; lean_object* v_env_207_; uint8_t v___x_208_; lean_object* v_env_209_; lean_object* v___x_210_; lean_object* v_toCold_211_; lean_object* v_mctx_212_; lean_object* v_lctx_213_; lean_object* v_options_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_206_ = lean_st_ref_get(v___y_204_);
v_env_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc_ref(v_env_207_);
lean_dec(v___x_206_);
v___x_208_ = 0;
v_env_209_ = l_Lean_Environment_setRecordingDeps(v_env_207_, v___x_208_);
v___x_210_ = lean_st_ref_get(v___y_202_);
v_toCold_211_ = lean_ctor_get(v___y_203_, 0);
v_mctx_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc_ref(v_mctx_212_);
lean_dec(v___x_210_);
v_lctx_213_ = lean_ctor_get(v___y_201_, 2);
v_options_214_ = lean_ctor_get(v_toCold_211_, 2);
lean_inc_ref(v_options_214_);
lean_inc_ref(v_lctx_213_);
v___x_215_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_215_, 0, v_env_209_);
lean_ctor_set(v___x_215_, 1, v_mctx_212_);
lean_ctor_set(v___x_215_, 2, v_lctx_213_);
lean_ctor_set(v___x_215_, 3, v_options_214_);
v___x_216_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v_msgData_200_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5___boxed(lean_object* v_msgData_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(v_msgData_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(lean_object* v_msg_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_ref_231_; lean_object* v___x_232_; lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_ref_231_ = lean_ctor_get(v___y_228_, 2);
v___x_232_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5_spec__5(v_msg_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
lean_inc(v_ref_231_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v_ref_231_);
lean_ctor_set(v___x_237_, 1, v_a_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 1);
lean_ctor_set(v___x_235_, 0, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg___boxed(lean_object* v_msg_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
return v_res_248_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__0));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__2));
v___x_254_ = l_Lean_stringToMessageData(v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__4));
v___x_257_ = l_Lean_stringToMessageData(v___x_256_);
return v___x_257_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__6));
v___x_260_ = l_Lean_stringToMessageData(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__8));
v___x_263_ = l_Lean_stringToMessageData(v___x_262_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__10));
v___x_266_ = l_Lean_stringToMessageData(v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(lean_object* v___x_267_, lean_object* v_declName_268_, lean_object* v_as_269_, size_t v_sz_270_, size_t v_i_271_, lean_object* v_b_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_a_279_; uint8_t v___x_283_; 
v___x_283_ = lean_usize_dec_lt(v_i_271_, v_sz_270_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
lean_dec(v_declName_268_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v_b_272_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v_a_286_; lean_object* v___x_287_; 
v___x_285_ = lean_box(0);
v_a_286_ = lean_array_uget_borrowed(v_as_269_, v_i_271_);
v___x_287_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_a_286_, v___y_273_, v___y_275_, v___y_276_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; uint8_t v___x_289_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_287_, 1);
v___x_289_ = l_Lean_LocalDecl_binderInfo(v_a_288_);
lean_dec(v_a_288_);
if (v___x_289_ == 3)
{
v_a_279_ = v___x_285_;
goto v___jp_278_;
}
else
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = l_Lean_Expr_fvarId_x21(v_a_286_);
v___x_291_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_290_, v___x_267_);
lean_dec(v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
lean_inc(v___y_276_);
lean_inc_ref(v___y_275_);
lean_inc(v___y_274_);
lean_inc_ref(v___y_273_);
lean_inc(v_a_286_);
v___x_292_ = lean_infer_type(v_a_286_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc_n(v_a_293_, 2);
lean_dec_ref_known(v___x_292_, 1);
v___x_294_ = l_Lean_Meta_isProp(v_a_293_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; uint8_t v___x_296_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v___x_296_ = lean_unbox(v_a_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_a_293_);
v___x_297_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__1);
lean_inc(v_a_286_);
v___x_298_ = l_Lean_MessageData_ofExpr(v_a_286_);
v___x_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__3);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_unbox(v_a_295_);
lean_dec(v_a_295_);
lean_inc(v_declName_268_);
v___x_303_ = l_Lean_MessageData_ofConstName(v_declName_268_, v___x_302_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_301_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__5);
v___x_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_306_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_dec_ref_known(v___x_307_, 1);
v_a_279_ = v___x_285_;
goto v___jp_278_;
}
else
{
lean_dec(v_declName_268_);
return v___x_307_;
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_a_295_);
v___x_308_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__7);
lean_inc(v_declName_268_);
v___x_309_ = l_Lean_MessageData_ofConstName(v_declName_268_, v___x_291_);
v___x_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__9);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = l_Lean_indentExpr(v_a_293_);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___closed__11);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_316_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_dec_ref_known(v___x_317_, 1);
v_a_279_ = v___x_285_;
goto v___jp_278_;
}
else
{
lean_dec(v_declName_268_);
return v___x_317_;
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec(v_a_293_);
lean_dec(v_declName_268_);
v_a_318_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_294_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_294_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec(v_declName_268_);
v_a_326_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_292_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_292_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
else
{
v_a_279_ = v___x_285_;
goto v___jp_278_;
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec(v_declName_268_);
v_a_334_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_287_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_287_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
v___jp_278_:
{
size_t v___x_280_; size_t v___x_281_; 
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_add(v_i_271_, v___x_280_);
v_i_271_ = v___x_281_;
v_b_272_ = v_a_279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6___boxed(lean_object* v___x_342_, lean_object* v_declName_343_, lean_object* v_as_344_, lean_object* v_sz_345_, lean_object* v_i_346_, lean_object* v_b_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
size_t v_sz_boxed_353_; size_t v_i_boxed_354_; lean_object* v_res_355_; 
v_sz_boxed_353_ = lean_unbox_usize(v_sz_345_);
lean_dec(v_sz_345_);
v_i_boxed_354_ = lean_unbox_usize(v_i_346_);
lean_dec(v_i_346_);
v_res_355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(v___x_342_, v_declName_343_, v_as_344_, v_sz_boxed_353_, v_i_boxed_354_, v_b_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec_ref(v_as_344_);
lean_dec(v___x_342_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(lean_object* v___x_356_, lean_object* v_as_357_, size_t v_sz_358_, size_t v_i_359_, lean_object* v_b_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = lean_usize_dec_lt(v_i_359_, v_sz_358_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
lean_dec(v___x_356_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_b_360_);
return v___x_367_;
}
else
{
lean_object* v_fst_368_; lean_object* v_snd_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_404_; 
v_fst_368_ = lean_ctor_get(v_b_360_, 0);
v_snd_369_ = lean_ctor_get(v_b_360_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_b_360_);
if (v_isSharedCheck_404_ == 0)
{
v___x_371_ = v_b_360_;
v_isShared_372_ = v_isSharedCheck_404_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_snd_369_);
lean_inc(v_fst_368_);
lean_dec(v_b_360_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_404_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v_a_373_; lean_object* v___x_374_; 
v_a_373_ = lean_array_uget_borrowed(v_as_357_, v_i_359_);
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
lean_inc(v___y_362_);
lean_inc_ref(v___y_361_);
lean_inc(v_a_373_);
v___x_374_ = lean_infer_type(v_a_373_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_395_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_395_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_395_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_395_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = l_Lean_Expr_fvarId_x21(v_a_373_);
v___x_387_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_386_, v_fst_368_);
lean_dec(v___x_386_);
if (v___x_387_ == 0)
{
lean_del_object(v___x_377_);
lean_dec(v_a_375_);
goto v___jp_379_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = l_Lean_Expr_containsFVar(v_a_375_, v___x_356_);
lean_dec(v_a_375_);
if (v___x_388_ == 0)
{
lean_del_object(v___x_377_);
goto v___jp_379_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
lean_del_object(v___x_371_);
lean_dec(v_snd_369_);
v___x_389_ = l_Lean_FVarIdSet_insert(v_fst_368_, v___x_356_);
v___x_390_ = lean_box(v___x_366_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_391_);
v___x_393_ = v___x_377_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
v___jp_379_:
{
lean_object* v___x_381_; 
if (v_isShared_372_ == 0)
{
v___x_381_ = v___x_371_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_fst_368_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_snd_369_);
v___x_381_ = v_reuseFailAlloc_385_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
size_t v___x_382_; size_t v___x_383_; 
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_add(v_i_359_, v___x_382_);
v_i_359_ = v___x_383_;
v_b_360_ = v___x_381_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_del_object(v___x_371_);
lean_dec(v_snd_369_);
lean_dec(v_fst_368_);
lean_dec(v___x_356_);
v_a_396_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_374_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_374_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1___boxed(lean_object* v___x_405_, lean_object* v_as_406_, lean_object* v_sz_407_, lean_object* v_i_408_, lean_object* v_b_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
size_t v_sz_boxed_415_; size_t v_i_boxed_416_; lean_object* v_res_417_; 
v_sz_boxed_415_ = lean_unbox_usize(v_sz_407_);
lean_dec(v_sz_407_);
v_i_boxed_416_ = lean_unbox_usize(v_i_408_);
lean_dec(v_i_408_);
v_res_417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(v___x_405_, v_as_406_, v_sz_boxed_415_, v_i_boxed_416_, v_b_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec_ref(v_as_406_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(lean_object* v_xs_418_, lean_object* v_as_419_, size_t v_sz_420_, size_t v_i_421_, lean_object* v_b_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_a_429_; uint8_t v___x_433_; 
v___x_433_ = lean_usize_dec_lt(v_i_421_, v_sz_420_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v_b_422_);
return v___x_434_;
}
else
{
lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_462_; 
v_fst_435_ = lean_ctor_get(v_b_422_, 0);
v_snd_436_ = lean_ctor_get(v_b_422_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_b_422_);
if (v_isSharedCheck_462_ == 0)
{
v___x_438_ = v_b_422_;
v_isShared_439_ = v_isSharedCheck_462_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_snd_436_);
lean_inc(v_fst_435_);
lean_dec(v_b_422_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_462_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_a_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_a_440_ = lean_array_uget_borrowed(v_as_419_, v_i_421_);
v___x_441_ = l_Lean_Expr_fvarId_x21(v_a_440_);
v___x_442_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v___x_441_, v_fst_435_);
if (v___x_442_ == 0)
{
lean_object* v___x_444_; 
if (v_isShared_439_ == 0)
{
v___x_444_ = v___x_438_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_fst_435_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_snd_436_);
v___x_444_ = v_reuseFailAlloc_458_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
size_t v_sz_445_; size_t v___x_446_; lean_object* v___x_447_; 
v_sz_445_ = lean_array_size(v_xs_418_);
v___x_446_ = ((size_t)0ULL);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__1(v___x_441_, v_xs_418_, v_sz_445_, v___x_446_, v___x_444_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v_fst_449_; lean_object* v_snd_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v_fst_449_ = lean_ctor_get(v_a_448_, 0);
v_snd_450_ = lean_ctor_get(v_a_448_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v_a_448_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_snd_450_);
lean_inc(v_fst_449_);
lean_dec(v_a_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_fst_449_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_snd_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
v_a_429_ = v___x_455_;
goto v___jp_428_;
}
}
}
else
{
return v___x_447_;
}
}
}
else
{
lean_object* v___x_460_; 
lean_dec(v___x_441_);
if (v_isShared_439_ == 0)
{
v___x_460_ = v___x_438_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_fst_435_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_snd_436_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
v_a_429_ = v___x_460_;
goto v___jp_428_;
}
}
}
}
v___jp_428_:
{
size_t v___x_430_; size_t v___x_431_; 
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_421_, v___x_430_);
v_i_421_ = v___x_431_;
v_b_422_ = v_a_429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2___boxed(lean_object* v_xs_463_, lean_object* v_as_464_, lean_object* v_sz_465_, lean_object* v_i_466_, lean_object* v_b_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
size_t v_sz_boxed_473_; size_t v_i_boxed_474_; lean_object* v_res_475_; 
v_sz_boxed_473_ = lean_unbox_usize(v_sz_465_);
lean_dec(v_sz_465_);
v_i_boxed_474_ = lean_unbox_usize(v_i_466_);
lean_dec(v_i_466_);
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(v_xs_463_, v_as_464_, v_sz_boxed_473_, v_i_boxed_474_, v_b_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v_as_464_);
lean_dec_ref(v_xs_463_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(lean_object* v_xs_476_, lean_object* v_a_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_snd_483_; uint8_t v___x_484_; 
v_snd_483_ = lean_ctor_get(v_a_477_, 1);
v___x_484_ = lean_unbox(v_snd_483_);
if (v___x_484_ == 0)
{
lean_object* v_fst_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_493_; 
lean_inc(v_snd_483_);
v_fst_485_ = lean_ctor_get(v_a_477_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_a_477_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v_a_477_, 1);
lean_dec(v_unused_494_);
v___x_487_ = v_a_477_;
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_fst_485_);
lean_dec(v_a_477_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_493_;
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
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_fst_485_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_snd_483_);
v___x_490_ = v_reuseFailAlloc_492_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; 
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
else
{
lean_object* v_fst_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_518_; 
v_fst_495_ = lean_ctor_get(v_a_477_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_a_477_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_a_477_, 1);
lean_dec(v_unused_519_);
v___x_497_ = v_a_477_;
v_isShared_498_ = v_isSharedCheck_518_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_fst_495_);
lean_dec(v_a_477_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_518_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_499_ = 0;
v___x_500_ = lean_box(v___x_499_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___x_500_);
v___x_502_ = v___x_497_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_fst_495_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_517_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
size_t v_sz_503_; size_t v___x_504_; lean_object* v___x_505_; 
v_sz_503_ = lean_array_size(v_xs_476_);
v___x_504_ = ((size_t)0ULL);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__2(v_xs_476_, v_xs_476_, v_sz_503_, v___x_504_, v___x_502_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v_fst_507_; lean_object* v_snd_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_516_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v_fst_507_ = lean_ctor_get(v_a_506_, 0);
v_snd_508_ = lean_ctor_get(v_a_506_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_a_506_);
if (v_isSharedCheck_516_ == 0)
{
v___x_510_ = v_a_506_;
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snd_508_);
lean_inc(v_fst_507_);
lean_dec(v_a_506_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_fst_507_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_snd_508_);
v___x_513_ = v_reuseFailAlloc_515_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
v_a_477_ = v___x_513_;
goto _start;
}
}
}
else
{
return v___x_505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg___boxed(lean_object* v_xs_520_, lean_object* v_a_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_520_, v_a_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v_xs_520_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(lean_object* v___y_528_, lean_object* v_as_529_, size_t v_sz_530_, size_t v_i_531_, lean_object* v_b_532_){
_start:
{
lean_object* v_a_535_; uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_lt(v_i_531_, v_sz_530_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_b_532_);
return v___x_540_;
}
else
{
lean_object* v_a_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v_a_541_ = lean_array_uget_borrowed(v_as_529_, v_i_531_);
v___x_542_ = l_Lean_Expr_fvarId_x21(v_a_541_);
v___x_543_ = l_Lean_Expr_containsFVar(v___y_528_, v___x_542_);
if (v___x_543_ == 0)
{
lean_dec(v___x_542_);
v_a_535_ = v_b_532_;
goto v___jp_534_;
}
else
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_FVarIdSet_insert(v_b_532_, v___x_542_);
v_a_535_ = v___x_544_;
goto v___jp_534_;
}
}
v___jp_534_:
{
size_t v___x_536_; size_t v___x_537_; 
v___x_536_ = ((size_t)1ULL);
v___x_537_ = lean_usize_add(v_i_531_, v___x_536_);
v_i_531_ = v___x_537_;
v_b_532_ = v_a_535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg___boxed(lean_object* v___y_545_, lean_object* v_as_546_, lean_object* v_sz_547_, lean_object* v_i_548_, lean_object* v_b_549_, lean_object* v___y_550_){
_start:
{
size_t v_sz_boxed_551_; size_t v_i_boxed_552_; lean_object* v_res_553_; 
v_sz_boxed_551_ = lean_unbox_usize(v_sz_547_);
lean_dec(v_sz_547_);
v_i_boxed_552_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_545_, v_as_546_, v_sz_boxed_551_, v_i_boxed_552_, v_b_549_);
lean_dec_ref(v_as_546_);
lean_dec_ref(v___y_545_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0(lean_object* v___x_563_, lean_object* v_declName_564_, lean_object* v_xs_565_, lean_object* v_concl_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; uint8_t v___x_573_; uint8_t v___x_574_; lean_object* v___y_576_; 
v___x_572_ = l_Lean_Expr_cleanupAnnotations(v_concl_566_);
v___x_573_ = l_Lean_Expr_isApp(v___x_572_);
v___x_574_ = 1;
if (v___x_573_ == 0)
{
lean_dec_ref(v___x_572_);
v___y_576_ = v_concl_566_;
goto v___jp_575_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_572_);
v___x_613_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__1));
v___x_614_ = l_Lean_Expr_isConstOf(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
uint8_t v___x_615_; 
lean_dec_ref(v___x_572_);
v___x_615_ = l_Lean_Expr_isApp(v___x_612_);
if (v___x_615_ == 0)
{
lean_dec_ref(v___x_612_);
v___y_576_ = v_concl_566_;
goto v___jp_575_;
}
else
{
lean_object* v_arg_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_arg_616_ = lean_ctor_get(v___x_612_, 1);
lean_inc_ref(v_arg_616_);
v___x_617_ = l_Lean_Expr_appFnCleanup___redArg(v___x_612_);
lean_dec_ref(v___x_612_);
v___x_618_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3));
v___x_619_ = l_Lean_Expr_isConstOf(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
uint8_t v___x_620_; 
v___x_620_ = l_Lean_Expr_isApp(v___x_617_);
if (v___x_620_ == 0)
{
lean_dec_ref(v___x_617_);
lean_dec_ref(v_arg_616_);
v___y_576_ = v_concl_566_;
goto v___jp_575_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = l_Lean_Expr_appFnCleanup___redArg(v___x_617_);
lean_dec_ref(v___x_617_);
v___x_622_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_623_ = l_Lean_Expr_isConstOf(v___x_621_, v___x_622_);
lean_dec_ref(v___x_621_);
if (v___x_623_ == 0)
{
lean_dec_ref(v_arg_616_);
v___y_576_ = v_concl_566_;
goto v___jp_575_;
}
else
{
lean_dec_ref(v_concl_566_);
v___y_576_ = v_arg_616_;
goto v___jp_575_;
}
}
}
else
{
lean_dec_ref(v___x_617_);
lean_dec_ref(v_concl_566_);
v___y_576_ = v_arg_616_;
goto v___jp_575_;
}
}
}
else
{
lean_object* v_arg_624_; 
lean_dec_ref(v___x_612_);
lean_dec_ref(v_concl_566_);
v_arg_624_ = lean_ctor_get(v___x_572_, 1);
lean_inc_ref(v_arg_624_);
lean_dec_ref(v___x_572_);
v___y_576_ = v_arg_624_;
goto v___jp_575_;
}
}
v___jp_575_:
{
size_t v_sz_577_; size_t v___x_578_; lean_object* v___x_579_; 
v_sz_577_ = lean_array_size(v_xs_565_);
v___x_578_ = ((size_t)0ULL);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_576_, v_xs_565_, v_sz_577_, v___x_578_, v___x_563_);
lean_dec_ref(v___y_576_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_579_, 1);
v___x_581_ = lean_box(v___x_574_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v_a_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_565_, v___x_582_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v_fst_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v_fst_585_ = lean_ctor_get(v_a_584_, 0);
lean_inc(v_fst_585_);
lean_dec(v_a_584_);
v___x_586_ = lean_box(0);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__6(v_fst_585_, v_declName_564_, v_xs_565_, v_sz_577_, v___x_578_, v___x_586_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v_fst_585_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v___x_587_, 0);
lean_dec(v_unused_595_);
v___x_589_ = v___x_587_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_dec(v___x_587_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_586_);
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_586_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
else
{
return v___x_587_;
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_declName_564_);
v_a_596_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_583_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_583_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_declName_564_);
v_a_604_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_579_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_579_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___lam__0___boxed(lean_object* v___x_625_, lean_object* v_declName_626_, lean_object* v_xs_627_, lean_object* v_concl_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_Grind_validateHomoTheorem___lam__0(v___x_625_, v_declName_626_, v_xs_627_, v_concl_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec_ref(v_xs_627_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(lean_object* v_ref_635_, lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_toCold_642_; lean_object* v_currRecDepth_643_; lean_object* v_ref_644_; uint16_t v_optionFlags_645_; uint8_t v_suppressElabErrors_646_; uint8_t v_checkDeprecated_647_; uint8_t v_isRecordingDeps_648_; lean_object* v_ref_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_toCold_642_ = lean_ctor_get(v___y_639_, 0);
v_currRecDepth_643_ = lean_ctor_get(v___y_639_, 1);
v_ref_644_ = lean_ctor_get(v___y_639_, 2);
v_optionFlags_645_ = lean_ctor_get_uint16(v___y_639_, sizeof(void*)*3);
v_suppressElabErrors_646_ = lean_ctor_get_uint8(v___y_639_, sizeof(void*)*3 + 2);
v_checkDeprecated_647_ = lean_ctor_get_uint8(v___y_639_, sizeof(void*)*3 + 3);
v_isRecordingDeps_648_ = lean_ctor_get_uint8(v___y_639_, sizeof(void*)*3 + 4);
v_ref_649_ = l_Lean_replaceRef(v_ref_635_, v_ref_644_);
lean_inc(v_currRecDepth_643_);
lean_inc_ref(v_toCold_642_);
v___x_650_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_650_, 0, v_toCold_642_);
lean_ctor_set(v___x_650_, 1, v_currRecDepth_643_);
lean_ctor_set(v___x_650_, 2, v_ref_649_);
lean_ctor_set_uint16(v___x_650_, sizeof(void*)*3, v_optionFlags_645_);
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*3 + 2, v_suppressElabErrors_646_);
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*3 + 3, v_checkDeprecated_647_);
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*3 + 4, v_isRecordingDeps_648_);
v___x_651_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_636_, v___y_637_, v___y_638_, v___x_650_, v___y_640_);
lean_dec_ref_known(v___x_650_, 3);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg___boxed(lean_object* v_ref_652_, lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_652_, v_msg_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v_ref_652_);
return v_res_659_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_660_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
lean_ctor_set(v___x_665_, 2, v___x_664_);
lean_ctor_set(v___x_665_, 3, v___x_664_);
lean_ctor_set(v___x_665_, 4, v___x_663_);
lean_ctor_set(v___x_665_, 5, v___x_663_);
lean_ctor_set(v___x_665_, 6, v___x_663_);
lean_ctor_set(v___x_665_, 7, v___x_663_);
lean_ctor_set(v___x_665_, 8, v___x_663_);
lean_ctor_set(v___x_665_, 9, v___x_663_);
lean_ctor_set(v___x_665_, 10, v___x_663_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_unsigned_to_nat(32u);
v___x_667_ = lean_mk_empty_array_with_capacity(v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_669_ = ((size_t)5ULL);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_unsigned_to_nat(32u);
v___x_672_ = lean_mk_empty_array_with_capacity(v___x_671_);
v___x_673_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_674_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_672_);
lean_ctor_set(v___x_674_, 2, v___x_670_);
lean_ctor_set(v___x_674_, 3, v___x_670_);
lean_ctor_set_usize(v___x_674_, 4, v___x_669_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_box(1);
v___x_676_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
lean_ctor_set(v___x_678_, 2, v___x_675_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_681_ = l_Lean_stringToMessageData(v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_684_ = l_Lean_stringToMessageData(v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_687_ = l_Lean_stringToMessageData(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_700_, lean_object* v_declHint_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v_env_706_; uint8_t v___x_707_; 
v___x_704_ = lean_box(0);
v___x_705_ = lean_st_ref_get(v___y_702_);
v_env_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc_ref(v_env_706_);
lean_dec(v___x_705_);
v___x_707_ = l_Lean_Name_isAnonymous(v_declHint_701_);
if (v___x_707_ == 0)
{
uint8_t v_isExporting_708_; 
v_isExporting_708_ = lean_ctor_get_uint8(v_env_706_, sizeof(void*)*13);
if (v_isExporting_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec_ref(v_env_706_);
lean_dec(v_declHint_701_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v_msg_700_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; uint8_t v___x_711_; 
lean_inc_ref(v_env_706_);
v___x_710_ = l_Lean_Environment_setExporting(v_env_706_, v___x_707_);
lean_inc(v_declHint_701_);
lean_inc_ref(v___x_710_);
v___x_711_ = l_Lean_Environment_contains(v___x_710_, v_declHint_701_, v_isExporting_708_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v___x_710_);
lean_dec_ref(v_env_706_);
lean_dec(v_declHint_701_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v_msg_700_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_c_718_; lean_object* v___x_719_; 
v___x_713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_714_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_715_ = l_Lean_Options_empty;
lean_inc_ref(v___x_710_);
v___x_716_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_716_, 0, v___x_710_);
lean_ctor_set(v___x_716_, 1, v___x_713_);
lean_ctor_set(v___x_716_, 2, v___x_714_);
lean_ctor_set(v___x_716_, 3, v___x_715_);
lean_inc(v_declHint_701_);
v___x_717_ = l_Lean_MessageData_ofConstName(v_declHint_701_, v___x_707_);
v_c_718_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_718_, 0, v___x_716_);
lean_ctor_set(v_c_718_, 1, v___x_717_);
v___x_719_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_710_, v_declHint_701_);
lean_dec_ref(v___x_710_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec_ref(v_env_706_);
lean_dec(v_declHint_701_);
v___x_720_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v_c_718_);
v___x_722_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l_Lean_MessageData_note(v___x_723_);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v_msg_700_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
else
{
lean_object* v_val_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_761_; 
v_val_727_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_761_ == 0)
{
v___x_729_ = v___x_719_;
v_isShared_730_ = v_isSharedCheck_761_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_val_727_);
lean_dec(v___x_719_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_761_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v_moduleNames_732_; lean_object* v_mod_733_; uint8_t v___x_734_; 
v___x_731_ = l_Lean_Environment_header(v_env_706_);
lean_dec_ref(v_env_706_);
v_moduleNames_732_ = lean_ctor_get(v___x_731_, 4);
lean_inc_ref(v_moduleNames_732_);
lean_dec_ref(v___x_731_);
v_mod_733_ = lean_array_get(v___x_704_, v_moduleNames_732_, v_val_727_);
lean_dec(v_val_727_);
lean_dec_ref(v_moduleNames_732_);
v___x_734_ = l_Lean_isPrivateName(v_declHint_701_);
lean_dec(v_declHint_701_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_735_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v_c_718_);
v___x_737_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_MessageData_ofName(v_mod_733_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_MessageData_note(v___x_742_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v_msg_700_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 0);
lean_ctor_set(v___x_729_, 0, v___x_744_);
v___x_746_ = v___x_729_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_748_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v_c_718_);
v___x_750_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_Lean_MessageData_ofName(v_mod_733_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = l_Lean_MessageData_note(v___x_755_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v_msg_700_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 0);
lean_ctor_set(v___x_729_, 0, v___x_757_);
v___x_759_ = v___x_729_;
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
}
}
}
else
{
lean_object* v___x_762_; 
lean_dec_ref(v_env_706_);
lean_dec(v_declHint_701_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v_msg_700_);
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_763_, lean_object* v_declHint_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_763_, v_declHint_764_, v___y_765_);
lean_dec(v___y_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_768_, lean_object* v_declHint_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_785_; 
v___x_775_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_768_, v_declHint_769_, v___y_773_);
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_785_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_785_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_785_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_780_ = l_Lean_unknownIdentifierMessageTag;
v___x_781_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v_a_776_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_781_);
v___x_783_ = v___x_778_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_786_, lean_object* v_declHint_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(v_msg_786_, v_declHint_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(lean_object* v_ref_794_, lean_object* v_msg_795_, lean_object* v_declHint_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; lean_object* v_a_803_; lean_object* v___x_804_; 
v___x_802_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12(v_msg_795_, v_declHint_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref(v___x_802_);
v___x_804_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_794_, v_a_803_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg___boxed(lean_object* v_ref_805_, lean_object* v_msg_806_, lean_object* v_declHint_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_805_, v_msg_806_, v_declHint_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v_ref_805_);
return v_res_813_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__0));
v___x_816_ = l_Lean_stringToMessageData(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__2));
v___x_819_ = l_Lean_stringToMessageData(v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_820_, lean_object* v_constName_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_827_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__1);
v___x_828_ = 0;
lean_inc(v_constName_821_);
v___x_829_ = l_Lean_MessageData_ofConstName(v_constName_821_, v___x_828_);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_827_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___closed__3);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_820_, v___x_832_, v_constName_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_834_, lean_object* v_constName_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_834_, v_constName_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v_ref_834_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(lean_object* v_constName_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_ref_848_; lean_object* v___x_849_; 
v_ref_848_ = lean_ctor_get(v___y_845_, 2);
v___x_849_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_848_, v_constName_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg___boxed(lean_object* v_constName_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(lean_object* v_constName_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; lean_object* v_env_864_; uint8_t v___x_865_; lean_object* v___x_866_; 
v___x_863_ = lean_st_ref_get(v___y_861_);
v_env_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc_ref(v_env_864_);
lean_dec(v___x_863_);
v___x_865_ = 0;
lean_inc(v_constName_857_);
v___x_866_ = l_Lean_Environment_find_x3f(v_env_864_, v_constName_857_, v___x_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_867_;
}
else
{
lean_object* v_val_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_constName_857_);
v_val_868_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_866_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_val_868_);
lean_dec(v___x_866_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 0);
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_val_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7___boxed(lean_object* v_constName_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_constName_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem(lean_object* v_declName_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_889_; lean_object* v___f_890_; lean_object* v___x_891_; 
v___x_889_ = lean_box(1);
lean_inc(v_declName_883_);
v___f_890_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___boxed), 9, 2);
lean_closure_set(v___f_890_, 0, v___x_889_);
lean_closure_set(v___f_890_, 1, v_declName_883_);
v___x_891_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
v___x_893_ = l_Lean_ConstantInfo_type(v_a_892_);
lean_dec(v_a_892_);
v___x_894_ = 0;
v___x_895_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_893_, v___f_890_, v___x_894_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
return v___x_895_;
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v___f_890_);
v_a_896_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_891_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_891_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateHomoTheorem___boxed(lean_object* v_declName_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Meta_Grind_validateHomoTheorem(v_declName_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_910_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0(lean_object* v_00_u03b2_911_, lean_object* v_k_912_, lean_object* v_t_913_){
_start:
{
uint8_t v___x_914_; 
v___x_914_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___redArg(v_k_912_, v_t_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0___boxed(lean_object* v_00_u03b2_915_, lean_object* v_k_916_, lean_object* v_t_917_){
_start:
{
uint8_t v_res_918_; lean_object* v_r_919_; 
v_res_918_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_validateHomoTheorem_spec__0(v_00_u03b2_915_, v_k_916_, v_t_917_);
lean_dec(v_t_917_);
lean_dec(v_k_916_);
v_r_919_ = lean_box(v_res_918_);
return v_r_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3(lean_object* v___y_920_, lean_object* v_as_921_, size_t v_sz_922_, size_t v_i_923_, lean_object* v_b_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___redArg(v___y_920_, v_as_921_, v_sz_922_, v_i_923_, v_b_924_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3___boxed(lean_object* v___y_931_, lean_object* v_as_932_, lean_object* v_sz_933_, lean_object* v_i_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_933_);
lean_dec(v_sz_933_);
v_i_boxed_942_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_validateHomoTheorem_spec__3(v___y_931_, v_as_932_, v_sz_boxed_941_, v_i_boxed_942_, v_b_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec_ref(v_as_932_);
lean_dec_ref(v___y_931_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4(lean_object* v_xs_944_, lean_object* v_inst_945_, lean_object* v_a_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___redArg(v_xs_944_, v_a_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4___boxed(lean_object* v_xs_953_, lean_object* v_inst_954_, lean_object* v_a_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_validateHomoTheorem_spec__4(v_xs_953_, v_inst_954_, v_a_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v_xs_953_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5(lean_object* v_00_u03b1_962_, lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v_msg_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___boxed(lean_object* v_00_u03b1_970_, lean_object* v_msg_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5(v_00_u03b1_970_, v_msg_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8(lean_object* v_00_u03b1_978_, lean_object* v_constName_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___redArg(v_constName_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8___boxed(lean_object* v_00_u03b1_986_, lean_object* v_constName_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8(v_00_u03b1_986_, v_constName_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_994_, lean_object* v_ref_995_, lean_object* v_constName_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___redArg(v_ref_995_, v_constName_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1003_, lean_object* v_ref_1004_, lean_object* v_constName_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10(v_00_u03b1_1003_, v_ref_1004_, v_constName_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v_ref_1004_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11(lean_object* v_00_u03b1_1012_, lean_object* v_ref_1013_, lean_object* v_msg_1014_, lean_object* v_declHint_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___redArg(v_ref_1013_, v_msg_1014_, v_declHint_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11___boxed(lean_object* v_00_u03b1_1022_, lean_object* v_ref_1023_, lean_object* v_msg_1024_, lean_object* v_declHint_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11(v_00_u03b1_1022_, v_ref_1023_, v_msg_1024_, v_declHint_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v_ref_1023_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13(lean_object* v_msg_1032_, lean_object* v_declHint_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg(v_msg_1032_, v_declHint_1033_, v___y_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1040_, lean_object* v_declHint_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13(v_msg_1040_, v_declHint_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13(lean_object* v_00_u03b1_1048_, lean_object* v_ref_1049_, lean_object* v_msg_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___redArg(v_ref_1049_, v_msg_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1057_, lean_object* v_ref_1058_, lean_object* v_msg_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__13(v_00_u03b1_1057_, v_ref_1058_, v_msg_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v_ref_1058_);
return v_res_1065_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__0));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__2));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__4));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0(lean_object* v_declName_1075_, lean_object* v_x_1076_, lean_object* v_concl_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___y_1087_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = l_Lean_Expr_cleanupAnnotations(v_concl_1077_);
v___x_1114_ = l_Lean_Expr_isApp(v___x_1113_);
if (v___x_1114_ == 0)
{
lean_dec_ref(v___x_1113_);
v___y_1087_ = v_concl_1077_;
goto v___jp_1086_;
}
else
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1113_);
lean_dec_ref(v___x_1113_);
v___x_1116_ = l_Lean_Expr_isApp(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_dec_ref(v___x_1115_);
v___y_1087_ = v_concl_1077_;
goto v___jp_1086_;
}
else
{
lean_object* v_arg_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v_arg_1117_ = lean_ctor_get(v___x_1115_, 1);
lean_inc_ref(v_arg_1117_);
v___x_1118_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1115_);
lean_dec_ref(v___x_1115_);
v___x_1119_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__3));
v___x_1120_ = l_Lean_Expr_isConstOf(v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; 
v___x_1121_ = l_Lean_Expr_isApp(v___x_1118_);
if (v___x_1121_ == 0)
{
lean_dec_ref(v___x_1118_);
lean_dec_ref(v_arg_1117_);
v___y_1087_ = v_concl_1077_;
goto v___jp_1086_;
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1118_);
lean_dec_ref(v___x_1118_);
v___x_1123_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_1124_ = l_Lean_Expr_isConstOf(v___x_1122_, v___x_1123_);
lean_dec_ref(v___x_1122_);
if (v___x_1124_ == 0)
{
lean_dec_ref(v_arg_1117_);
v___y_1087_ = v_concl_1077_;
goto v___jp_1086_;
}
else
{
lean_dec_ref(v_concl_1077_);
v___y_1087_ = v_arg_1117_;
goto v___jp_1086_;
}
}
}
else
{
lean_dec_ref(v___x_1118_);
lean_dec_ref(v_concl_1077_);
v___y_1087_ = v_arg_1117_;
goto v___jp_1086_;
}
}
}
v___jp_1083_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
v___jp_1086_:
{
lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = l_Lean_Expr_cleanupAnnotations(v___y_1087_);
lean_dec_ref(v___y_1087_);
v___x_1089_ = l_Lean_Expr_isApp(v___x_1088_);
if (v___x_1089_ == 0)
{
lean_dec_ref(v___x_1088_);
lean_dec(v_declName_1075_);
goto v___jp_1083_;
}
else
{
lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1088_);
lean_dec_ref(v___x_1088_);
v___x_1091_ = l_Lean_Expr_isApp(v___x_1090_);
if (v___x_1091_ == 0)
{
lean_dec_ref(v___x_1090_);
lean_dec(v_declName_1075_);
goto v___jp_1083_;
}
else
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1090_);
lean_dec_ref(v___x_1090_);
v___x_1093_ = l_Lean_Expr_isApp(v___x_1092_);
if (v___x_1093_ == 0)
{
lean_dec_ref(v___x_1092_);
lean_dec(v_declName_1075_);
goto v___jp_1083_;
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1094_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1092_);
v___x_1095_ = ((lean_object*)(l_Lean_Meta_Grind_validateHomoTheorem___lam__0___closed__5));
v___x_1096_ = l_Lean_Expr_isConstOf(v___x_1094_, v___x_1095_);
lean_dec_ref(v___x_1094_);
if (v___x_1096_ == 0)
{
lean_dec_ref(v___x_1092_);
lean_dec(v_declName_1075_);
goto v___jp_1083_;
}
else
{
lean_object* v_arg_1097_; lean_object* v___x_1098_; 
v_arg_1097_ = lean_ctor_get(v___x_1092_, 1);
lean_inc_ref(v_arg_1097_);
lean_dec_ref(v___x_1092_);
v___x_1098_ = l_Lean_Expr_getAppFn(v_arg_1097_);
if (lean_obj_tag(v___x_1098_) == 4)
{
lean_object* v_declName_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec_ref(v_arg_1097_);
lean_dec(v_declName_1075_);
v_declName_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_declName_1099_);
lean_dec_ref_known(v___x_1098_, 2);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_declName_1099_);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec_ref(v___x_1098_);
v___x_1102_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__1);
v___x_1103_ = 0;
v___x_1104_ = l_Lean_MessageData_ofConstName(v_declName_1075_, v___x_1103_);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1102_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__3);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = l_Lean_indentExpr(v_arg_1097_);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___closed__5);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1111_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1112_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___boxed(lean_object* v_declName_1125_, lean_object* v_x_1126_, lean_object* v_concl_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0(v_declName_1125_, v_x_1126_, v_concl_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_x_1126_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(lean_object* v_declName_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___f_1140_; lean_object* v___x_1141_; 
lean_inc(v_declName_1134_);
v___f_1140_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1140_, 0, v_declName_1134_);
v___x_1141_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = l_Lean_ConstantInfo_type(v_a_1142_);
lean_dec(v_a_1142_);
v___x_1144_ = 0;
v___x_1145_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_1143_, v___f_1140_, v___x_1144_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
return v___x_1145_;
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v___f_1140_);
v_a_1146_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1141_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1141_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f___boxed(lean_object* v_declName_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(v_declName_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
return v_res_1160_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg___closed__0);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___dummy_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg();
return v_res_1166_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7_spec__8_spec__10_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1___redArg();
return v___x_1171_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0);
v___x_1176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
lean_ctor_set(v___x_1176_, 2, v___x_1174_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1177_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__4, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__4);
v___x_1178_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__3);
v___x_1179_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__0);
v___x_1180_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2);
v___x_1181_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v___x_1179_);
lean_ctor_set(v___x_1181_, 2, v___x_1178_);
lean_ctor_set(v___x_1181_, 3, v___x_1179_);
lean_ctor_set(v___x_1181_, 4, v___x_1179_);
lean_ctor_set(v___x_1181_, 5, v___x_1179_);
lean_ctor_set(v___x_1181_, 6, v___x_1179_);
lean_ctor_set(v___x_1181_, 7, v___x_1177_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(lean_object* v_ext_1182_, lean_object* v_b_1183_, uint8_t v_kind_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_toCold_1189_; lean_object* v_currNamespace_1190_; lean_object* v___x_1191_; lean_object* v_env_1192_; lean_object* v_nextMacroScope_1193_; lean_object* v_ngen_1194_; lean_object* v_auxDeclNGen_1195_; lean_object* v_traceState_1196_; lean_object* v_recordedDeps_1197_; lean_object* v_messages_1198_; lean_object* v_infoState_1199_; lean_object* v_snapshotTasks_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1227_; 
v_toCold_1189_ = lean_ctor_get(v___y_1186_, 0);
v_currNamespace_1190_ = lean_ctor_get(v_toCold_1189_, 4);
v___x_1191_ = lean_st_ref_take(v___y_1187_);
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
v_nextMacroScope_1193_ = lean_ctor_get(v___x_1191_, 1);
v_ngen_1194_ = lean_ctor_get(v___x_1191_, 2);
v_auxDeclNGen_1195_ = lean_ctor_get(v___x_1191_, 3);
v_traceState_1196_ = lean_ctor_get(v___x_1191_, 4);
v_recordedDeps_1197_ = lean_ctor_get(v___x_1191_, 6);
v_messages_1198_ = lean_ctor_get(v___x_1191_, 7);
v_infoState_1199_ = lean_ctor_get(v___x_1191_, 8);
v_snapshotTasks_1200_ = lean_ctor_get(v___x_1191_, 9);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; 
v_unused_1228_ = lean_ctor_get(v___x_1191_, 5);
lean_dec(v_unused_1228_);
v___x_1202_ = v___x_1191_;
v_isShared_1203_ = v_isSharedCheck_1227_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_snapshotTasks_1200_);
lean_inc(v_infoState_1199_);
lean_inc(v_messages_1198_);
lean_inc(v_recordedDeps_1197_);
lean_inc(v_traceState_1196_);
lean_inc(v_auxDeclNGen_1195_);
lean_inc(v_ngen_1194_);
lean_inc(v_nextMacroScope_1193_);
lean_inc(v_env_1192_);
lean_dec(v___x_1191_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1227_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
lean_inc(v_currNamespace_1190_);
v___x_1204_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1192_, v_ext_1182_, v_b_1183_, v_kind_1184_, v_currNamespace_1190_);
v___x_1205_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__1);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 5, v___x_1205_);
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1207_ = v___x_1202_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_nextMacroScope_1193_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_ngen_1194_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_auxDeclNGen_1195_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_traceState_1196_);
lean_ctor_set(v_reuseFailAlloc_1226_, 5, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1226_, 6, v_recordedDeps_1197_);
lean_ctor_set(v_reuseFailAlloc_1226_, 7, v_messages_1198_);
lean_ctor_set(v_reuseFailAlloc_1226_, 8, v_infoState_1199_);
lean_ctor_set(v_reuseFailAlloc_1226_, 9, v_snapshotTasks_1200_);
v___x_1207_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_mctx_1210_; lean_object* v_zetaDeltaFVarIds_1211_; lean_object* v_postponed_1212_; lean_object* v_diag_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1224_; 
v___x_1208_ = lean_st_ref_put(v___y_1187_, v___x_1207_);
v___x_1209_ = lean_st_ref_take(v___y_1185_);
v_mctx_1210_ = lean_ctor_get(v___x_1209_, 0);
v_zetaDeltaFVarIds_1211_ = lean_ctor_get(v___x_1209_, 2);
v_postponed_1212_ = lean_ctor_get(v___x_1209_, 3);
v_diag_1213_ = lean_ctor_get(v___x_1209_, 4);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v___x_1209_, 1);
lean_dec(v_unused_1225_);
v___x_1215_ = v___x_1209_;
v_isShared_1216_ = v_isSharedCheck_1224_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_diag_1213_);
lean_inc(v_postponed_1212_);
lean_inc(v_zetaDeltaFVarIds_1211_);
lean_inc(v_mctx_1210_);
lean_dec(v___x_1209_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1224_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1217_ = lean_box(0);
v___x_1218_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__5);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v___x_1218_);
v___x_1220_ = v___x_1215_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_mctx_1210_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_zetaDeltaFVarIds_1211_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v_postponed_1212_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_diag_1213_);
v___x_1220_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_st_ref_put(v___y_1185_, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1217_);
return v___x_1222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___boxed(lean_object* v_ext_1229_, lean_object* v_b_1230_, lean_object* v_kind_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
uint8_t v_kind_boxed_1236_; lean_object* v_res_1237_; 
v_kind_boxed_1236_ = lean_unbox(v_kind_1231_);
v_res_1237_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v_ext_1229_, v_b_1230_, v_kind_boxed_1236_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0(uint8_t v_attrKind_1238_, lean_object* v_declName_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
lean_inc(v_declName_1239_);
v___x_1245_ = l_Lean_Meta_Grind_validateHomoTheorem(v_declName_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; 
lean_dec_ref_known(v___x_1245_, 1);
v___x_1246_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_checkEqInjection_x3f(v_declName_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1258_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1258_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1258_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
if (lean_obj_tag(v_a_1247_) == 1)
{
lean_object* v_val_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_del_object(v___x_1249_);
v_val_1251_ = lean_ctor_get(v_a_1247_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v_a_1247_, 1);
v___x_1252_ = l_Lean_Meta_Grind_homoSourceTypesExt;
v___x_1253_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v___x_1252_, v_val_1251_, v_attrKind_1238_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
lean_dec(v_a_1247_);
v___x_1254_ = lean_box(0);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1254_);
v___x_1256_ = v___x_1249_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
v_a_1259_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1246_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1246_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
lean_dec(v_declName_1239_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed(lean_object* v_attrKind_1267_, lean_object* v_declName_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
uint8_t v_attrKind_boxed_1274_; lean_object* v_res_1275_; 
v_attrKind_boxed_1274_ = lean_unbox(v_attrKind_1267_);
v_res_1275_ = l_Lean_Meta_Grind_addHomoAttr___lam__0(v_attrKind_boxed_1274_, v_declName_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object* v_declName_1276_, uint8_t v_attrKind_1277_, uint8_t v_fallback_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1284_; lean_object* v_validate_1285_; 
v___x_1284_ = lean_box(v_attrKind_1277_);
v_validate_1285_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoAttr___lam__0___boxed), 7, 1);
lean_closure_set(v_validate_1285_, 0, v___x_1284_);
if (v_fallback_1278_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = l_Lean_Meta_Grind_homoExt;
v___x_1287_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v___x_1286_, v_declName_1276_, v_attrKind_1277_, v_validate_1285_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; 
lean_dec_ref(v_validate_1285_);
lean_inc(v_declName_1276_);
v___x_1288_ = l_Lean_Meta_Grind_addHomoAttr___lam__0(v_attrKind_1277_, v_declName_1276_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1289_; 
lean_dec_ref_known(v___x_1288_, 1);
v___x_1289_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_1276_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v_expr_1291_; lean_object* v_pattern_1292_; lean_object* v_rhs_1293_; uint8_t v_perm_1294_; lean_object* v_rhsVarMask_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1304_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1289_, 1);
v_expr_1291_ = lean_ctor_get(v_a_1290_, 0);
v_pattern_1292_ = lean_ctor_get(v_a_1290_, 1);
v_rhs_1293_ = lean_ctor_get(v_a_1290_, 2);
v_perm_1294_ = lean_ctor_get_uint8(v_a_1290_, sizeof(void*)*4);
v_rhsVarMask_1295_ = lean_ctor_get(v_a_1290_, 3);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_a_1290_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1297_ = v_a_1290_;
v_isShared_1298_ = v_isSharedCheck_1304_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_rhsVarMask_1295_);
lean_inc(v_rhs_1293_);
lean_inc(v_pattern_1292_);
lean_inc(v_expr_1291_);
lean_dec(v_a_1290_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1304_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = l_Lean_Meta_Grind_homoExt;
if (v_isShared_1298_ == 0)
{
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_expr_1291_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_pattern_1292_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_rhs_1293_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_rhsVarMask_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1303_, sizeof(void*)*4, v_perm_1294_);
v___x_1301_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; 
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*4 + 1, v_fallback_1278_);
v___x_1302_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v___x_1299_, v___x_1301_, v_attrKind_1277_, v_a_1280_, v_a_1281_, v_a_1282_);
return v___x_1302_;
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
v_a_1305_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1289_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1289_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_dec(v_declName_1276_);
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoAttr___boxed(lean_object* v_declName_1313_, lean_object* v_attrKind_1314_, lean_object* v_fallback_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
uint8_t v_attrKind_boxed_1321_; uint8_t v_fallback_boxed_1322_; lean_object* v_res_1323_; 
v_attrKind_boxed_1321_ = lean_unbox(v_attrKind_1314_);
v_fallback_boxed_1322_ = lean_unbox(v_fallback_1315_);
v_res_1323_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_1313_, v_attrKind_boxed_1321_, v_fallback_boxed_1322_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(lean_object* v_00_u03b1_1324_, lean_object* v_00_u03b2_1325_, lean_object* v_00_u03c3_1326_, lean_object* v_ext_1327_, lean_object* v_b_1328_, uint8_t v_kind_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v_ext_1327_, v_b_1328_, v_kind_1329_, v___y_1331_, v___y_1332_, v___y_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___boxed(lean_object* v_00_u03b1_1336_, lean_object* v_00_u03b2_1337_, lean_object* v_00_u03c3_1338_, lean_object* v_ext_1339_, lean_object* v_b_1340_, lean_object* v_kind_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
uint8_t v_kind_boxed_1347_; lean_object* v_res_1348_; 
v_kind_boxed_1347_ = lean_unbox(v_kind_1341_);
v_res_1348_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0(v_00_u03b1_1336_, v_00_u03b2_1337_, v_00_u03c3_1338_, v_ext_1339_, v_b_1340_, v_kind_boxed_1347_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0___redArg();
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0_spec__0(lean_object* v_00_u03b2_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg___closed__2);
return v___x_1356_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(lean_object* v_x_1362_, lean_object* v_x_1363_){
_start:
{
lean_object* v_declName_1364_; lean_object* v_arity_1365_; lean_object* v_declName_1366_; lean_object* v_arity_1367_; uint8_t v___x_1368_; 
v_declName_1364_ = lean_ctor_get(v_x_1362_, 0);
v_arity_1365_ = lean_ctor_get(v_x_1362_, 1);
v_declName_1366_ = lean_ctor_get(v_x_1363_, 0);
v_arity_1367_ = lean_ctor_get(v_x_1363_, 1);
v___x_1368_ = lean_name_eq(v_declName_1364_, v_declName_1366_);
if (v___x_1368_ == 0)
{
return v___x_1368_;
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = lean_nat_dec_eq(v_arity_1365_, v_arity_1367_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq___boxed(lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
uint8_t v_res_1372_; lean_object* v_r_1373_; 
v_res_1372_ = l_Lean_Meta_Grind_instBEqHomoPredTheorem_beq(v_x_1370_, v_x_1371_);
lean_dec_ref(v_x_1371_);
lean_dec_ref(v_x_1370_);
v_r_1373_ = lean_box(v_res_1372_);
return v_r_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object* v_x_1376_, lean_object* v_a_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v_a_1377_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object* v_x_1381_, lean_object* v_a_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(v_x_1381_, v_a_1382_, v___y_1383_);
lean_dec_ref(v___y_1383_);
lean_dec(v_x_1381_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object* v_x_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_a_1387_);
lean_inc_ref_n(v___x_1388_, 2);
v___x_1389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
lean_ctor_set(v___x_1389_, 2, v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object* v_x_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(v_x_1390_, v_a_1391_);
lean_dec_ref(v_x_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(lean_object* v_s_1393_, lean_object* v_x_1394_){
_start:
{
lean_object* v_fst_1395_; lean_object* v_snd_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1409_; 
v_fst_1395_ = lean_ctor_get(v_x_1394_, 0);
v_snd_1396_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1398_ = v_x_1394_;
v_isShared_1399_ = v_isSharedCheck_1409_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_snd_1396_);
lean_inc(v_fst_1395_);
lean_dec(v_x_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1409_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___y_1401_; lean_object* v___x_1406_; 
v___x_1406_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_s_1393_, v_fst_1395_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_box(0);
v___y_1401_ = v___x_1407_;
goto v___jp_1400_;
}
else
{
lean_object* v_val_1408_; 
v_val_1408_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v___x_1406_, 1);
v___y_1401_ = v_val_1408_;
goto v___jp_1400_;
}
v___jp_1400_:
{
lean_object* v___x_1403_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set_tag(v___x_1398_, 1);
lean_ctor_set(v___x_1398_, 1, v___y_1401_);
lean_ctor_set(v___x_1398_, 0, v_snd_1396_);
v___x_1403_ = v___x_1398_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_snd_1396_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v___y_1401_);
v___x_1403_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1395_, v___x_1403_, v_s_1393_);
return v___x_1404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_));
v___x_1436_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2____boxed(lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l___private_Lean_Meta_Tactic_Grind_Homo_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Homo_2929944344____hygCtx___hyg_2_();
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg(lean_object* v_a_1439_){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v_env_1443_; lean_object* v___x_1444_; lean_object* v_ext_1445_; lean_object* v_toEnvExtension_1446_; lean_object* v_asyncMode_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1441_ = lean_box(1);
v___x_1442_ = lean_st_ref_get(v_a_1439_);
v_env_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc_ref(v_env_1443_);
lean_dec(v___x_1442_);
v___x_1444_ = l_Lean_Meta_Grind_homoPredExt;
v_ext_1445_ = lean_ctor_get(v___x_1444_, 1);
v_toEnvExtension_1446_ = lean_ctor_get(v_ext_1445_, 0);
v_asyncMode_1447_ = lean_ctor_get(v_toEnvExtension_1446_, 2);
v___x_1448_ = 0;
v___x_1449_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1441_, v___x_1444_, v_env_1443_, v_asyncMode_1447_, v___x_1448_);
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg___boxed(lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1451_);
lean_dec(v_a_1451_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems(lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___boxed(lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_Meta_Grind_getHomoPredTheorems(v_a_1458_, v_a_1459_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(lean_object* v_msg_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___f_1469_; lean_object* v___x_2185__overap_1470_; lean_object* v___x_1471_; 
v___f_1469_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___closed__0));
v___x_2185__overap_1470_ = lean_panic_fn_borrowed(v___f_1469_, v_msg_1463_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
v___x_1471_ = lean_apply_5(v___x_2185__overap_1470_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, lean_box(0));
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1___boxed(lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(v_msg_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1478_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(lean_object* v_xs_1479_, lean_object* v_ys_1480_, lean_object* v_x_1481_){
_start:
{
lean_object* v_zero_1482_; uint8_t v_isZero_1483_; 
v_zero_1482_ = lean_unsigned_to_nat(0u);
v_isZero_1483_ = lean_nat_dec_eq(v_x_1481_, v_zero_1482_);
if (v_isZero_1483_ == 1)
{
lean_dec(v_x_1481_);
return v_isZero_1483_;
}
else
{
lean_object* v_one_1484_; lean_object* v_n_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v_one_1484_ = lean_unsigned_to_nat(1u);
v_n_1485_ = lean_nat_sub(v_x_1481_, v_one_1484_);
lean_dec(v_x_1481_);
v___x_1486_ = lean_array_fget_borrowed(v_xs_1479_, v_n_1485_);
v___x_1487_ = lean_array_fget_borrowed(v_ys_1480_, v_n_1485_);
v___x_1488_ = lean_expr_eqv(v___x_1486_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_dec(v_n_1485_);
return v___x_1488_;
}
else
{
v_x_1481_ = v_n_1485_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg___boxed(lean_object* v_xs_1490_, lean_object* v_ys_1491_, lean_object* v_x_1492_){
_start:
{
uint8_t v_res_1493_; lean_object* v_r_1494_; 
v_res_1493_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v_xs_1490_, v_ys_1491_, v_x_1492_);
lean_dec_ref(v_ys_1491_);
lean_dec_ref(v_xs_1490_);
v_r_1494_ = lean_box(v_res_1493_);
return v_r_1494_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1495_; lean_object* v_dummy_1496_; 
v___x_1495_ = lean_box(0);
v_dummy_1496_ = l_Lean_Expr_sort___override(v___x_1495_);
return v_dummy_1496_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_addHomoPredAttr___lam__0(lean_object* v_a_1497_, lean_object* v_e_1498_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = l_Lean_Expr_isApp(v_e_1498_);
if (v___x_1499_ == 0)
{
lean_dec_ref(v_e_1498_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = l_Lean_Expr_getAppFn(v_e_1498_);
v___x_1501_ = l_Lean_Expr_isConst(v___x_1500_);
lean_dec_ref(v___x_1500_);
if (v___x_1501_ == 0)
{
lean_dec_ref(v_e_1498_);
return v___x_1501_;
}
else
{
lean_object* v_dummy_1502_; lean_object* v_nargs_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_dummy_1502_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0, &l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0);
v_nargs_1503_ = l_Lean_Expr_getAppNumArgs(v_e_1498_);
lean_inc(v_nargs_1503_);
v___x_1504_ = lean_mk_array(v_nargs_1503_, v_dummy_1502_);
v___x_1505_ = lean_unsigned_to_nat(1u);
v___x_1506_ = lean_nat_sub(v_nargs_1503_, v___x_1505_);
lean_dec(v_nargs_1503_);
v___x_1507_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1498_, v___x_1504_, v___x_1506_);
v___x_1508_ = lean_array_get_size(v___x_1507_);
v___x_1509_ = lean_array_get_size(v_a_1497_);
v___x_1510_ = lean_nat_dec_lt(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1511_ = lean_nat_sub(v___x_1508_, v___x_1509_);
v___x_1512_ = l_Array_extract___redArg(v___x_1507_, v___x_1511_, v___x_1508_);
lean_dec_ref(v___x_1507_);
v___x_1513_ = lean_array_get_size(v___x_1512_);
v___x_1514_ = lean_nat_dec_eq(v___x_1513_, v___x_1509_);
if (v___x_1514_ == 0)
{
lean_dec_ref(v___x_1512_);
return v___x_1514_;
}
else
{
uint8_t v___x_1515_; 
v___x_1515_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v___x_1512_, v_a_1497_, v___x_1513_);
lean_dec_ref(v___x_1512_);
return v___x_1515_;
}
}
else
{
uint8_t v___x_1516_; 
lean_dec_ref(v___x_1507_);
v___x_1516_ = 0;
return v___x_1516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__0___boxed(lean_object* v_a_1517_, lean_object* v_e_1518_){
_start:
{
uint8_t v_res_1519_; lean_object* v_r_1520_; 
v_res_1519_ = l_Lean_Meta_Grind_addHomoPredAttr___lam__0(v_a_1517_, v_e_1518_);
lean_dec_ref(v_a_1517_);
v_r_1520_ = lean_box(v_res_1519_);
return v_r_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(lean_object* v_as_1521_, size_t v_i_1522_, size_t v_stop_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_a_1530_; uint8_t v___x_1534_; 
v___x_1534_ = lean_usize_dec_eq(v_i_1522_, v_stop_1523_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_array_uget_borrowed(v_as_1521_, v_i_1522_);
v___x_1536_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_1535_, v___y_1525_, v___y_1526_, v___y_1527_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; uint8_t v___x_1538_; uint8_t v___x_1539_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1538_ = l_Lean_LocalDecl_binderInfo(v_a_1537_);
lean_dec(v_a_1537_);
v___x_1539_ = l_Lean_BinderInfo_isExplicit(v___x_1538_);
if (v___x_1539_ == 0)
{
v_a_1530_ = v_b_1524_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1540_; 
lean_inc(v___x_1535_);
v___x_1540_ = lean_array_push(v_b_1524_, v___x_1535_);
v_a_1530_ = v___x_1540_;
goto v___jp_1529_;
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_b_1524_);
v_a_1541_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1536_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1536_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_b_1524_);
return v___x_1549_;
}
v___jp_1529_:
{
size_t v___x_1531_; size_t v___x_1532_; 
v___x_1531_ = ((size_t)1ULL);
v___x_1532_ = lean_usize_add(v_i_1522_, v___x_1531_);
v_i_1522_ = v___x_1532_;
v_b_1524_ = v_a_1530_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg___boxed(lean_object* v_as_1550_, lean_object* v_i_1551_, lean_object* v_stop_1552_, lean_object* v_b_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
size_t v_i_boxed_1558_; size_t v_stop_boxed_1559_; lean_object* v_res_1560_; 
v_i_boxed_1558_ = lean_unbox_usize(v_i_1551_);
lean_dec(v_i_1551_);
v_stop_boxed_1559_ = lean_unbox_usize(v_stop_1552_);
lean_dec(v_stop_1552_);
v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_as_1550_, v_i_boxed_1558_, v_stop_boxed_1559_, v_b_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec_ref(v_as_1550_);
return v_res_1560_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1564_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__2));
v___x_1565_ = lean_unsigned_to_nat(41u);
v___x_1566_ = lean_unsigned_to_nat(169u);
v___x_1567_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__1));
v___x_1568_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__0));
v___x_1569_ = l_mkPanicMessageWithDecl(v___x_1568_, v___x_1567_, v___x_1566_, v___x_1565_, v___x_1564_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__4));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__6));
v___x_1575_ = l_Lean_stringToMessageData(v___x_1574_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__8));
v___x_1578_ = l_Lean_stringToMessageData(v___x_1577_);
return v___x_1578_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__10));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1(lean_object* v_declName_1584_, uint8_t v_attrKind_1585_, lean_object* v_xs_1586_, lean_object* v_type_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v_a_1615_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = lean_array_get_size(v_xs_1586_);
v___x_1629_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__12));
v___x_1630_ = lean_nat_dec_lt(v___x_1627_, v___x_1628_);
if (v___x_1630_ == 0)
{
v_a_1615_ = v___x_1629_;
goto v___jp_1614_;
}
else
{
size_t v___x_1631_; size_t v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = lean_usize_of_nat(v___x_1628_);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_xs_1586_, v___x_1631_, v___x_1632_, v___x_1629_, v___y_1588_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v_a_1615_ = v_a_1634_;
goto v___jp_1614_;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec(v_declName_1584_);
v_a_1635_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1633_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1633_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
v___jp_1593_:
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_find_expr(v___y_1595_, v_type_1587_);
lean_dec_ref(v___y_1595_);
if (lean_obj_tag(v___x_1596_) == 1)
{
lean_object* v_val_1597_; lean_object* v___x_1598_; 
v_val_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_val_1597_);
lean_dec_ref_known(v___x_1596_, 1);
v___x_1598_ = l_Lean_Expr_getAppFn(v_val_1597_);
lean_dec(v_val_1597_);
if (lean_obj_tag(v___x_1598_) == 4)
{
lean_object* v_declName_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_declName_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_declName_1599_);
lean_dec_ref_known(v___x_1598_, 2);
v___x_1600_ = l_Lean_Meta_Grind_homoPredExt;
v___x_1601_ = lean_array_get_size(v___y_1594_);
lean_dec_ref(v___y_1594_);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_declName_1584_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v_declName_1599_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addHomoAttr_spec__0___redArg(v___x_1600_, v___x_1603_, v_attrKind_1585_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec_ref(v___x_1598_);
lean_dec_ref(v___y_1594_);
lean_dec(v_declName_1584_);
v___x_1605_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__3);
v___x_1606_ = l_panic___at___00Lean_Meta_Grind_addHomoPredAttr_spec__1(v___x_1605_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1606_;
}
}
else
{
lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec(v___x_1596_);
lean_dec_ref(v___y_1594_);
v___x_1607_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__5);
v___x_1608_ = 0;
v___x_1609_ = l_Lean_MessageData_ofConstName(v_declName_1584_, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1607_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__7);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1612_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1613_;
}
}
v___jp_1614_:
{
lean_object* v___f_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
lean_inc_ref(v_a_1615_);
v___f_1616_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1616_, 0, v_a_1615_);
v___x_1617_ = lean_array_get_size(v_a_1615_);
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = lean_nat_dec_eq(v___x_1617_, v___x_1618_);
if (v___x_1619_ == 0)
{
v___y_1594_ = v_a_1615_;
v___y_1595_ = v___f_1616_;
goto v___jp_1593_;
}
else
{
lean_object* v___x_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_dec_ref(v___f_1616_);
lean_dec_ref(v_a_1615_);
v___x_1620_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9);
v___x_1621_ = 0;
v___x_1622_ = l_Lean_MessageData_ofConstName(v_declName_1584_, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1620_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__11);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1625_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___lam__1___boxed(lean_object* v_declName_1643_, lean_object* v_attrKind_1644_, lean_object* v_xs_1645_, lean_object* v_type_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
uint8_t v_attrKind_boxed_1652_; lean_object* v_res_1653_; 
v_attrKind_boxed_1652_ = lean_unbox(v_attrKind_1644_);
v_res_1653_ = l_Lean_Meta_Grind_addHomoPredAttr___lam__1(v_declName_1643_, v_attrKind_boxed_1652_, v_xs_1645_, v_type_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec_ref(v_type_1646_);
lean_dec_ref(v_xs_1645_);
return v_res_1653_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addHomoPredAttr___closed__1(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Meta_Grind_addHomoPredAttr___closed__0));
v___x_1656_ = l_Lean_stringToMessageData(v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object* v_declName_1657_, uint8_t v_attrKind_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1664_; lean_object* v___f_1665_; lean_object* v___x_1666_; 
v___x_1664_ = lean_box(v_attrKind_1658_);
lean_inc_n(v_declName_1657_, 2);
v___f_1665_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addHomoPredAttr___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1665_, 0, v_declName_1657_);
lean_closure_set(v___f_1665_, 1, v___x_1664_);
v___x_1666_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_validateHomoTheorem_spec__7(v_declName_1657_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___x_1676_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = l_Lean_ConstantInfo_type(v_a_1667_);
lean_dec(v_a_1667_);
lean_inc_ref(v___x_1668_);
v___x_1676_ = l_Lean_Meta_isProp(v___x_1668_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; uint8_t v___x_1678_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v___x_1678_ = lean_unbox(v_a_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec_ref(v___x_1668_);
lean_dec_ref(v___f_1665_);
v___x_1679_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9, &l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__1___closed__9);
v___x_1680_ = lean_unbox(v_a_1677_);
lean_dec(v_a_1677_);
v___x_1681_ = l_Lean_MessageData_ofConstName(v_declName_1657_, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1679_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___closed__1, &l_Lean_Meta_Grind_addHomoPredAttr___closed__1_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___closed__1);
v___x_1684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateHomoTheorem_spec__5___redArg(v___x_1684_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
return v___x_1685_;
}
else
{
lean_dec(v_a_1677_);
lean_dec(v_declName_1657_);
v___y_1670_ = v_a_1659_;
v___y_1671_ = v_a_1660_;
v___y_1672_ = v_a_1661_;
v___y_1673_ = v_a_1662_;
goto v___jp_1669_;
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v___x_1668_);
lean_dec_ref(v___f_1665_);
lean_dec(v_declName_1657_);
v_a_1686_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1676_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1676_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
v___jp_1669_:
{
uint8_t v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = 0;
v___x_1675_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Grind_validateHomoTheorem_spec__8___redArg(v___x_1668_, v___f_1665_, v___x_1674_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
return v___x_1675_;
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v___f_1665_);
lean_dec(v_declName_1657_);
v_a_1694_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1666_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1666_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHomoPredAttr___boxed(lean_object* v_declName_1702_, lean_object* v_attrKind_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
uint8_t v_attrKind_boxed_1709_; lean_object* v_res_1710_; 
v_attrKind_boxed_1709_ = lean_unbox(v_attrKind_1703_);
v_res_1710_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_1702_, v_attrKind_boxed_1709_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
return v_res_1710_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0(lean_object* v_xs_1711_, lean_object* v_ys_1712_, lean_object* v_hsz_1713_, lean_object* v_x_1714_, lean_object* v_x_1715_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___redArg(v_xs_1711_, v_ys_1712_, v_x_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0___boxed(lean_object* v_xs_1717_, lean_object* v_ys_1718_, lean_object* v_hsz_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_){
_start:
{
uint8_t v_res_1722_; lean_object* v_r_1723_; 
v_res_1722_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_addHomoPredAttr_spec__0(v_xs_1717_, v_ys_1718_, v_hsz_1719_, v_x_1720_, v_x_1721_);
lean_dec_ref(v_ys_1718_);
lean_dec_ref(v_xs_1717_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2(lean_object* v_as_1724_, size_t v_i_1725_, size_t v_stop_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___redArg(v_as_1724_, v_i_1725_, v_stop_1726_, v_b_1727_, v___y_1728_, v___y_1730_, v___y_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2___boxed(lean_object* v_as_1734_, lean_object* v_i_1735_, lean_object* v_stop_1736_, lean_object* v_b_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
size_t v_i_boxed_1743_; size_t v_stop_boxed_1744_; lean_object* v_res_1745_; 
v_i_boxed_1743_ = lean_unbox_usize(v_i_1735_);
lean_dec(v_i_1735_);
v_stop_boxed_1744_ = lean_unbox_usize(v_stop_1736_);
lean_dec(v_stop_1736_);
v_res_1745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_addHomoPredAttr_spec__2(v_as_1734_, v_i_boxed_1743_, v_stop_boxed_1744_, v_b_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v_as_1734_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(lean_object* v___x_1746_, lean_object* v_as_x27_1747_, lean_object* v_b_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
if (lean_obj_tag(v_as_x27_1747_) == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_b_1748_);
return v___x_1754_;
}
else
{
lean_object* v_head_1755_; lean_object* v_tail_1756_; lean_object* v_a_1758_; lean_object* v_declName_1764_; lean_object* v_arity_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v_head_1755_ = lean_ctor_get(v_as_x27_1747_, 0);
v_tail_1756_ = lean_ctor_get(v_as_x27_1747_, 1);
v_declName_1764_ = lean_ctor_get(v_head_1755_, 0);
v_arity_1765_ = lean_ctor_get(v_head_1755_, 1);
v___x_1766_ = lean_array_get_size(v___x_1746_);
v___x_1767_ = lean_nat_dec_le(v_arity_1765_, v___x_1766_);
if (v___x_1767_ == 0)
{
v_as_x27_1747_ = v_tail_1756_;
goto _start;
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_nat_sub(v___x_1766_, v_arity_1765_);
v___x_1770_ = l_Array_extract___redArg(v___x_1746_, v___x_1769_, v___x_1766_);
lean_inc(v_declName_1764_);
v___x_1771_ = l_Lean_Meta_mkAppM(v_declName_1764_, v___x_1770_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1773_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc_n(v_a_1772_, 2);
lean_dec_ref_known(v___x_1771_, 1);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
v___x_1773_ = lean_infer_type(v_a_1772_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_a_1772_);
lean_ctor_set(v___x_1775_, 1, v_a_1774_);
v___x_1776_ = lean_array_push(v_b_1748_, v___x_1775_);
v_as_x27_1747_ = v_tail_1756_;
v_b_1748_ = v___x_1776_;
goto _start;
}
else
{
lean_object* v_a_1778_; 
lean_dec(v_a_1772_);
v_a_1778_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1773_, 1);
v_a_1758_ = v_a_1778_;
goto v___jp_1757_;
}
}
else
{
lean_object* v_a_1779_; 
v_a_1779_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1771_, 1);
v_a_1758_ = v_a_1779_;
goto v___jp_1757_;
}
}
v___jp_1757_:
{
uint8_t v___x_1759_; 
v___x_1759_ = l_Lean_Exception_isInterrupt(v_a_1758_);
if (v___x_1759_ == 0)
{
uint8_t v___x_1760_; 
lean_inc_ref(v_a_1758_);
v___x_1760_ = l_Lean_Exception_isRuntime(v_a_1758_);
if (v___x_1760_ == 0)
{
lean_dec_ref(v_a_1758_);
v_as_x27_1747_ = v_tail_1756_;
goto _start;
}
else
{
lean_object* v___x_1762_; 
lean_dec_ref(v_b_1748_);
v___x_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_a_1758_);
return v___x_1762_;
}
}
else
{
lean_object* v___x_1763_; 
lean_dec_ref(v_b_1748_);
v___x_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1763_, 0, v_a_1758_);
return v___x_1763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg___boxed(lean_object* v___x_1780_, lean_object* v_as_x27_1781_, lean_object* v_b_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1780_, v_as_x27_1781_, v_b_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v_as_x27_1781_);
lean_dec_ref(v___x_1780_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHomoPredInstances(lean_object* v_e_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_Expr_getAppFn(v_e_1791_);
if (lean_obj_tag(v___x_1797_) == 4)
{
lean_object* v_declName_1798_; lean_object* v___x_1799_; lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1818_; 
v_declName_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_declName_1798_);
lean_dec_ref_known(v___x_1797_, 2);
v___x_1799_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_1795_);
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1818_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1818_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1800_, v_declName_1798_);
lean_dec(v_declName_1798_);
lean_dec(v_a_1800_);
if (lean_obj_tag(v___x_1804_) == 1)
{
lean_object* v_val_1805_; lean_object* v_dummy_1806_; lean_object* v_nargs_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_del_object(v___x_1802_);
v_val_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v_dummy_1806_ = lean_obj_once(&l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0, &l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_addHomoPredAttr___lam__0___closed__0);
v_nargs_1807_ = l_Lean_Expr_getAppNumArgs(v_e_1791_);
lean_inc(v_nargs_1807_);
v___x_1808_ = lean_mk_array(v_nargs_1807_, v_dummy_1806_);
v___x_1809_ = lean_unsigned_to_nat(1u);
v___x_1810_ = lean_nat_sub(v_nargs_1807_, v___x_1809_);
lean_dec(v_nargs_1807_);
v___x_1811_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1791_, v___x_1808_, v___x_1810_);
v___x_1812_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
v___x_1813_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1811_, v_val_1805_, v___x_1812_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
lean_dec(v_val_1805_);
lean_dec_ref(v___x_1811_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
lean_dec(v___x_1804_);
lean_dec_ref(v_e_1791_);
v___x_1814_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1814_);
v___x_1816_ = v___x_1802_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec_ref(v___x_1797_);
lean_dec_ref(v_e_1791_);
v___x_1819_ = ((lean_object*)(l_Lean_Meta_Grind_mkHomoPredInstances___closed__0));
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkHomoPredInstances___boxed(lean_object* v_e_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Meta_Grind_mkHomoPredInstances(v_e_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0(lean_object* v___x_1828_, lean_object* v_as_1829_, lean_object* v_as_x27_1830_, lean_object* v_b_1831_, lean_object* v_a_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___redArg(v___x_1828_, v_as_x27_1830_, v_b_1831_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0___boxed(lean_object* v___x_1839_, lean_object* v_as_1840_, lean_object* v_as_x27_1841_, lean_object* v_b_1842_, lean_object* v_a_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkHomoPredInstances_spec__0(v___x_1839_, v_as_1840_, v_as_x27_1841_, v_b_1842_, v_a_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v_as_x27_1841_);
lean_dec(v_as_1840_);
lean_dec_ref(v___x_1839_);
return v_res_1849_;
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
