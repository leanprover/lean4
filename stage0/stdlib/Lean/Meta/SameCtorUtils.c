// Lean compiler output
// Module: Lean.Meta.SameCtorUtils
// Imports: public import Lean.Meta.Basic import Lean.Meta.Transform
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
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_occursOrInType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursOrInType___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_occursInCtorTypeMask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_occursInCtorTypeMask___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_occursInCtorTypeMask___closed__0 = (const lean_object*)&l_Lean_Meta_occursInCtorTypeMask___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: t.isForall\n        "};
static const lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Meta.SameCtorUtils.0.Lean.Meta.withSharedCtorIndices.go"};
static const lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.SameCtorUtils"};
static const lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0;
static const lean_array_object l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(lean_object* v_lctx_1_, lean_object* v_e_2_, lean_object* v_s_3_){
_start:
{
if (lean_obj_tag(v_s_3_) == 1)
{
lean_object* v_fvarId_4_; lean_object* v___x_5_; 
v_fvarId_4_ = lean_ctor_get(v_s_3_, 0);
lean_inc(v_fvarId_4_);
v___x_5_ = lean_local_ctx_find(v_lctx_1_, v_fvarId_4_);
if (lean_obj_tag(v___x_5_) == 1)
{
lean_object* v_val_6_; uint8_t v___x_7_; 
v_val_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_expr_eqv(v_s_3_, v_e_2_);
lean_dec_ref(v_s_3_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = l_Lean_LocalDecl_type(v_val_6_);
lean_dec(v_val_6_);
v___x_9_ = l_Lean_Expr_occurs(v_e_2_, v___x_8_);
lean_dec_ref(v___x_8_);
return v___x_9_;
}
else
{
lean_dec(v_val_6_);
lean_dec_ref(v_e_2_);
return v___x_7_;
}
}
else
{
uint8_t v___x_10_; 
lean_dec(v___x_5_);
v___x_10_ = lean_expr_eqv(v_s_3_, v_e_2_);
lean_dec_ref(v_e_2_);
lean_dec_ref(v_s_3_);
return v___x_10_;
}
}
else
{
uint8_t v___x_11_; 
lean_dec_ref(v_lctx_1_);
v___x_11_ = lean_expr_eqv(v_s_3_, v_e_2_);
lean_dec_ref(v_e_2_);
lean_dec_ref(v_s_3_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed(lean_object* v_lctx_12_, lean_object* v_e_13_, lean_object* v_s_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(v_lctx_12_, v_e_13_, v_s_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_occursOrInType(lean_object* v_lctx_17_, lean_object* v_e_18_, lean_object* v_t_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed), 3, 2);
lean_closure_set(v___x_20_, 0, v_lctx_17_);
lean_closure_set(v___x_20_, 1, v_e_18_);
v___x_21_ = lean_find_expr(v___x_20_, v_t_19_);
lean_dec_ref(v___x_20_);
if (lean_obj_tag(v___x_21_) == 0)
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
else
{
uint8_t v___x_23_; 
lean_dec_ref(v___x_21_);
v___x_23_ = 1;
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursOrInType___boxed(lean_object* v_lctx_24_, lean_object* v_e_25_, lean_object* v_t_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Lean_Meta_occursOrInType(v_lctx_24_, v_e_25_, v_t_26_);
lean_dec_ref(v_t_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(lean_object* v_k_29_, lean_object* v_b_30_, lean_object* v_c_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
v___x_37_ = lean_apply_7(v_k_29_, v_b_30_, v_c_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, lean_box(0));
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed(lean_object* v_k_38_, lean_object* v_b_39_, lean_object* v_c_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(v_k_38_, v_b_39_, v_c_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(lean_object* v_type_47_, lean_object* v_maxFVars_x3f_48_, lean_object* v_k_49_, uint8_t v_cleanupAnnotations_50_, uint8_t v_whnfType_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___f_57_; lean_object* v___x_58_; 
v___f_57_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_57_, 0, v_k_49_);
v___x_58_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_47_, v_maxFVars_x3f_48_, v___f_57_, v_cleanupAnnotations_50_, v_whnfType_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
v_a_67_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_58_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_58_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___boxed(lean_object* v_type_75_, lean_object* v_maxFVars_x3f_76_, lean_object* v_k_77_, lean_object* v_cleanupAnnotations_78_, lean_object* v_whnfType_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_85_; uint8_t v_whnfType_boxed_86_; lean_object* v_res_87_; 
v_cleanupAnnotations_boxed_85_ = lean_unbox(v_cleanupAnnotations_78_);
v_whnfType_boxed_86_ = lean_unbox(v_whnfType_79_);
v_res_87_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_type_75_, v_maxFVars_x3f_76_, v_k_77_, v_cleanupAnnotations_boxed_85_, v_whnfType_boxed_86_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2(lean_object* v_00_u03b1_88_, lean_object* v_type_89_, lean_object* v_maxFVars_x3f_90_, lean_object* v_k_91_, uint8_t v_cleanupAnnotations_92_, uint8_t v_whnfType_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_type_89_, v_maxFVars_x3f_90_, v_k_91_, v_cleanupAnnotations_92_, v_whnfType_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___boxed(lean_object* v_00_u03b1_100_, lean_object* v_type_101_, lean_object* v_maxFVars_x3f_102_, lean_object* v_k_103_, lean_object* v_cleanupAnnotations_104_, lean_object* v_whnfType_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_111_; uint8_t v_whnfType_boxed_112_; lean_object* v_res_113_; 
v_cleanupAnnotations_boxed_111_ = lean_unbox(v_cleanupAnnotations_104_);
v_whnfType_boxed_112_ = lean_unbox(v_whnfType_105_);
v_res_113_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2(v_00_u03b1_100_, v_type_101_, v_maxFVars_x3f_102_, v_k_103_, v_cleanupAnnotations_boxed_111_, v_whnfType_boxed_112_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(lean_object* v___x_114_, lean_object* v_a_115_, size_t v_sz_116_, size_t v_i_117_, lean_object* v_bs_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_usize_dec_lt(v_i_117_, v_sz_116_);
if (v___x_119_ == 0)
{
lean_dec_ref(v___x_114_);
return v_bs_118_;
}
else
{
lean_object* v_v_120_; lean_object* v___x_121_; lean_object* v_bs_x27_122_; uint8_t v___x_123_; size_t v___x_124_; size_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_v_120_ = lean_array_uget(v_bs_118_, v_i_117_);
v___x_121_ = lean_unsigned_to_nat(0u);
v_bs_x27_122_ = lean_array_uset(v_bs_118_, v_i_117_, v___x_121_);
lean_inc_ref(v___x_114_);
v___x_123_ = l_Lean_Meta_occursOrInType(v___x_114_, v_v_120_, v_a_115_);
v___x_124_ = ((size_t)1ULL);
v___x_125_ = lean_usize_add(v_i_117_, v___x_124_);
v___x_126_ = lean_box(v___x_123_);
v___x_127_ = lean_array_uset(v_bs_x27_122_, v_i_117_, v___x_126_);
v_i_117_ = v___x_125_;
v_bs_118_ = v___x_127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0___boxed(lean_object* v___x_129_, lean_object* v_a_130_, lean_object* v_sz_131_, lean_object* v_i_132_, lean_object* v_bs_133_){
_start:
{
size_t v_sz_boxed_134_; size_t v_i_boxed_135_; lean_object* v_res_136_; 
v_sz_boxed_134_ = lean_unbox_usize(v_sz_131_);
lean_dec(v_sz_131_);
v_i_boxed_135_ = lean_unbox_usize(v_i_132_);
lean_dec(v_i_132_);
v_res_136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(v___x_129_, v_a_130_, v_sz_boxed_134_, v_i_boxed_135_, v_bs_133_);
lean_dec_ref(v_a_130_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__0(lean_object* v_ys_137_, lean_object* v_ctorRet_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___x_144_; 
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
lean_inc(v___y_140_);
lean_inc_ref(v___y_139_);
v___x_144_ = lean_whnf(v_ctorRet_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_146_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_a_145_);
lean_dec_ref(v___x_144_);
v___x_146_ = l_Lean_Core_betaReduce(v_a_145_, v___y_141_, v___y_142_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_158_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_158_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_158_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_158_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v_lctx_151_; size_t v_sz_152_; size_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v_lctx_151_ = lean_ctor_get(v___y_139_, 2);
lean_inc_ref(v_lctx_151_);
lean_dec_ref(v___y_139_);
v_sz_152_ = lean_array_size(v_ys_137_);
v___x_153_ = ((size_t)0ULL);
v___x_154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(v_lctx_151_, v_a_147_, v_sz_152_, v___x_153_, v_ys_137_);
lean_dec(v_a_147_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_154_);
v___x_156_ = v___x_149_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec_ref(v___y_139_);
lean_dec_ref(v_ys_137_);
v_a_159_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_146_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_146_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref(v___y_139_);
lean_dec_ref(v_ys_137_);
v_a_167_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_144_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_144_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__0___boxed(lean_object* v_ys_175_, lean_object* v_ctorRet_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Meta_occursInCtorTypeMask___lam__0(v_ys_175_, v_ctorRet_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__1(lean_object* v_numFields_183_, lean_object* v___f_184_, lean_object* v_x_185_, lean_object* v_ctorRet_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_numFields_183_);
v___x_193_ = 0;
v___x_194_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_ctorRet_186_, v___x_192_, v___f_184_, v___x_193_, v___x_193_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__1___boxed(lean_object* v_numFields_195_, lean_object* v___f_196_, lean_object* v_x_197_, lean_object* v_ctorRet_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Meta_occursInCtorTypeMask___lam__1(v_numFields_195_, v___f_196_, v_x_197_, v_ctorRet_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec_ref(v_x_197_);
return v_res_204_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_instMonadEIO(lean_box(0));
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_toApplicative_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_279_; 
v___x_216_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0);
v___x_217_ = l_StateRefT_x27_instMonad___redArg(v___x_216_);
v_toApplicative_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v___x_217_, 1);
lean_dec(v_unused_280_);
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_279_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_toApplicative_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_279_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_toFunctor_222_; lean_object* v_toSeq_223_; lean_object* v_toSeqLeft_224_; lean_object* v_toSeqRight_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_277_; 
v_toFunctor_222_ = lean_ctor_get(v_toApplicative_218_, 0);
v_toSeq_223_ = lean_ctor_get(v_toApplicative_218_, 2);
v_toSeqLeft_224_ = lean_ctor_get(v_toApplicative_218_, 3);
v_toSeqRight_225_ = lean_ctor_get(v_toApplicative_218_, 4);
v_isSharedCheck_277_ = !lean_is_exclusive(v_toApplicative_218_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v_toApplicative_218_, 1);
lean_dec(v_unused_278_);
v___x_227_ = v_toApplicative_218_;
v_isShared_228_ = v_isSharedCheck_277_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_toSeqRight_225_);
lean_inc(v_toSeqLeft_224_);
lean_inc(v_toSeq_223_);
lean_inc(v_toFunctor_222_);
lean_dec(v_toApplicative_218_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_277_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___f_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___x_233_; lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v___x_238_; 
v___f_229_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1));
v___f_230_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2));
lean_inc_ref(v_toFunctor_222_);
v___f_231_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_231_, 0, v_toFunctor_222_);
v___f_232_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_232_, 0, v_toFunctor_222_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v___f_231_);
lean_ctor_set(v___x_233_, 1, v___f_232_);
v___f_234_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_234_, 0, v_toSeqRight_225_);
v___f_235_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_235_, 0, v_toSeqLeft_224_);
v___f_236_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_236_, 0, v_toSeq_223_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 4, v___f_234_);
lean_ctor_set(v___x_227_, 3, v___f_235_);
lean_ctor_set(v___x_227_, 2, v___f_236_);
lean_ctor_set(v___x_227_, 1, v___f_229_);
lean_ctor_set(v___x_227_, 0, v___x_233_);
v___x_238_ = v___x_227_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___f_229_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v___f_236_);
lean_ctor_set(v_reuseFailAlloc_276_, 3, v___f_235_);
lean_ctor_set(v_reuseFailAlloc_276_, 4, v___f_234_);
v___x_238_ = v_reuseFailAlloc_276_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___f_230_);
lean_ctor_set(v___x_220_, 0, v___x_238_);
v___x_240_ = v___x_220_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___f_230_);
v___x_240_ = v_reuseFailAlloc_275_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; lean_object* v_toApplicative_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_273_; 
v___x_241_ = l_StateRefT_x27_instMonad___redArg(v___x_240_);
v_toApplicative_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v___x_241_, 1);
lean_dec(v_unused_274_);
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_273_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_toApplicative_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_273_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_toFunctor_246_; lean_object* v_toSeq_247_; lean_object* v_toSeqLeft_248_; lean_object* v_toSeqRight_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_271_; 
v_toFunctor_246_ = lean_ctor_get(v_toApplicative_242_, 0);
v_toSeq_247_ = lean_ctor_get(v_toApplicative_242_, 2);
v_toSeqLeft_248_ = lean_ctor_get(v_toApplicative_242_, 3);
v_toSeqRight_249_ = lean_ctor_get(v_toApplicative_242_, 4);
v_isSharedCheck_271_ = !lean_is_exclusive(v_toApplicative_242_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v_toApplicative_242_, 1);
lean_dec(v_unused_272_);
v___x_251_ = v_toApplicative_242_;
v_isShared_252_ = v_isSharedCheck_271_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_toSeqRight_249_);
lean_inc(v_toSeqLeft_248_);
lean_inc(v_toSeq_247_);
lean_inc(v_toFunctor_246_);
lean_dec(v_toApplicative_242_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_271_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___f_260_; lean_object* v___x_262_; 
v___f_253_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3));
v___f_254_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4));
lean_inc_ref(v_toFunctor_246_);
v___f_255_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_255_, 0, v_toFunctor_246_);
v___f_256_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_256_, 0, v_toFunctor_246_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___f_255_);
lean_ctor_set(v___x_257_, 1, v___f_256_);
v___f_258_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_258_, 0, v_toSeqRight_249_);
v___f_259_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_259_, 0, v_toSeqLeft_248_);
v___f_260_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_260_, 0, v_toSeq_247_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 4, v___f_258_);
lean_ctor_set(v___x_251_, 3, v___f_259_);
lean_ctor_set(v___x_251_, 2, v___f_260_);
lean_ctor_set(v___x_251_, 1, v___f_253_);
lean_ctor_set(v___x_251_, 0, v___x_257_);
v___x_262_ = v___x_251_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___f_253_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v___f_260_);
lean_ctor_set(v_reuseFailAlloc_270_, 3, v___f_259_);
lean_ctor_set(v_reuseFailAlloc_270_, 4, v___f_258_);
v___x_262_ = v_reuseFailAlloc_270_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_264_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___f_254_);
lean_ctor_set(v___x_244_, 0, v___x_262_);
v___x_264_ = v___x_244_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v___f_254_);
v___x_264_ = v_reuseFailAlloc_269_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_2065__overap_267_; lean_object* v___x_268_; 
v___x_265_ = lean_box(0);
v___x_266_ = l_instInhabitedOfMonad___redArg(v___x_264_, v___x_265_);
v___x_2065__overap_267_ = lean_panic_fn(v___x_266_, v_msg_210_);
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
lean_inc(v___y_212_);
lean_inc_ref(v___y_211_);
v___x_268_ = lean_apply_5(v___x_2065__overap_267_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, lean_box(0));
return v___x_268_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___boxed(lean_object* v_msg_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v_msg_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(lean_object* v_msgData_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v___x_294_; lean_object* v_env_295_; lean_object* v___x_296_; lean_object* v_mctx_297_; lean_object* v_lctx_298_; lean_object* v_options_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_294_ = lean_st_ref_get(v___y_292_);
v_env_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc_ref(v_env_295_);
lean_dec(v___x_294_);
v___x_296_ = lean_st_ref_get(v___y_290_);
v_mctx_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc_ref(v_mctx_297_);
lean_dec(v___x_296_);
v_lctx_298_ = lean_ctor_get(v___y_289_, 2);
v_options_299_ = lean_ctor_get(v___y_291_, 2);
lean_inc_ref(v_options_299_);
lean_inc_ref(v_lctx_298_);
v___x_300_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_300_, 0, v_env_295_);
lean_ctor_set(v___x_300_, 1, v_mctx_297_);
lean_ctor_set(v___x_300_, 2, v_lctx_298_);
lean_ctor_set(v___x_300_, 3, v_options_299_);
v___x_301_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_msgData_288_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msgData_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(lean_object* v_msg_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_ref_316_; lean_object* v___x_317_; lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_326_; 
v_ref_316_ = lean_ctor_get(v___y_313_, 5);
v___x_317_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msg_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_326_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
lean_inc(v_ref_316_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v_ref_316_);
lean_ctor_set(v___x_322_, 1, v_a_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 1);
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg___boxed(lean_object* v_msg_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_333_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0));
v___x_336_ = l_Lean_stringToMessageData(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2));
v___x_339_ = l_Lean_stringToMessageData(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_343_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6));
v___x_344_ = lean_unsigned_to_nat(11u);
v___x_345_ = lean_unsigned_to_nat(122u);
v___x_346_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5));
v___x_347_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4));
v___x_348_ = l_mkPanicMessageWithDecl(v___x_347_, v___x_346_, v___x_345_, v___x_344_, v___x_343_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(lean_object* v_constName_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_363_; lean_object* v_env_364_; uint8_t v___x_365_; lean_object* v___x_366_; 
v___x_363_ = lean_st_ref_get(v___y_353_);
v_env_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc_ref(v_env_364_);
lean_dec(v___x_363_);
v___x_365_ = 0;
lean_inc(v_constName_349_);
v___x_366_ = l_Lean_Environment_findAsync_x3f(v_env_364_, v_constName_349_, v___x_365_);
if (lean_obj_tag(v___x_366_) == 1)
{
lean_object* v_val_367_; uint8_t v_kind_368_; 
v_val_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_val_367_);
lean_dec_ref(v___x_366_);
v_kind_368_ = lean_ctor_get_uint8(v_val_367_, sizeof(void*)*3);
if (v_kind_368_ == 6)
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_367_);
if (lean_obj_tag(v___x_369_) == 6)
{
lean_object* v_val_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_constName_349_);
v_val_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_val_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 0);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_val_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec_ref(v___x_369_);
v___x_378_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7);
v___x_379_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v___x_378_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_388_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_388_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
if (lean_obj_tag(v_a_380_) == 0)
{
lean_del_object(v___x_382_);
goto v___jp_355_;
}
else
{
lean_object* v_val_384_; lean_object* v___x_386_; 
lean_dec(v_constName_349_);
v_val_384_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_val_384_);
lean_dec_ref(v_a_380_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_val_384_);
v___x_386_ = v___x_382_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_val_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v_constName_349_);
v_a_389_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_379_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_379_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
else
{
lean_dec(v_val_367_);
goto v___jp_355_;
}
}
else
{
lean_dec(v___x_366_);
goto v___jp_355_;
}
v___jp_355_:
{
lean_object* v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_356_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
v___x_357_ = 0;
v___x_358_ = l_Lean_MessageData_ofConstName(v_constName_349_, v___x_357_);
v___x_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_356_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_361_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___boxed(lean_object* v_constName_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(v_constName_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask(lean_object* v_ctorName_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(v_ctorName_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v_toConstantVal_413_; lean_object* v_numParams_414_; lean_object* v_numFields_415_; lean_object* v_type_416_; lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___x_419_; uint8_t v___x_420_; lean_object* v___x_421_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v___x_411_);
v_toConstantVal_413_ = lean_ctor_get(v_a_412_, 0);
lean_inc_ref(v_toConstantVal_413_);
v_numParams_414_ = lean_ctor_get(v_a_412_, 3);
lean_inc(v_numParams_414_);
v_numFields_415_ = lean_ctor_get(v_a_412_, 4);
lean_inc(v_numFields_415_);
lean_dec(v_a_412_);
v_type_416_ = lean_ctor_get(v_toConstantVal_413_, 2);
lean_inc_ref(v_type_416_);
lean_dec_ref(v_toConstantVal_413_);
v___f_417_ = ((lean_object*)(l_Lean_Meta_occursInCtorTypeMask___closed__0));
v___f_418_ = lean_alloc_closure((void*)(l_Lean_Meta_occursInCtorTypeMask___lam__1___boxed), 9, 2);
lean_closure_set(v___f_418_, 0, v_numFields_415_);
lean_closure_set(v___f_418_, 1, v___f_417_);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_numParams_414_);
v___x_420_ = 0;
v___x_421_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_type_416_, v___x_419_, v___f_418_, v___x_420_, v___x_420_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_421_;
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
v_a_422_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_411_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_411_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___boxed(lean_object* v_ctorName_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_occursInCtorTypeMask(v_ctorName_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(lean_object* v_00_u03b1_437_, lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___boxed(lean_object* v_00_u03b1_445_, lean_object* v_msg_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(v_00_u03b1_445_, v_msg_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(lean_object* v_msg_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___f_460_; lean_object* v___x_685__overap_461_; lean_object* v___x_462_; 
v___f_460_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0));
v___x_685__overap_461_ = lean_panic_fn(v___f_460_, v_msg_454_);
lean_inc(v___y_458_);
lean_inc_ref(v___y_457_);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
v___x_462_ = lean_apply_5(v___x_685__overap_461_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, lean_box(0));
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___boxed(lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(lean_object* v_00_u03b1_470_, lean_object* v_msg_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___boxed(lean_object* v_00_u03b1_478_, lean_object* v_msg_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(v_00_u03b1_478_, v_msg_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(lean_object* v_k_486_, lean_object* v_b_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; 
lean_inc(v___y_491_);
lean_inc_ref(v___y_490_);
lean_inc(v___y_489_);
lean_inc_ref(v___y_488_);
v___x_493_ = lean_apply_6(v_k_486_, v_b_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, lean_box(0));
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_494_, lean_object* v_b_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(v_k_494_, v_b_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(lean_object* v_name_502_, uint8_t v_bi_503_, lean_object* v_type_504_, lean_object* v_k_505_, uint8_t v_kind_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___f_512_; lean_object* v___x_513_; 
v___f_512_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_512_, 0, v_k_505_);
v___x_513_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_502_, v_bi_503_, v_type_504_, v___f_512_, v_kind_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_a_522_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_513_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_513_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___boxed(lean_object* v_name_530_, lean_object* v_bi_531_, lean_object* v_type_532_, lean_object* v_k_533_, lean_object* v_kind_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
uint8_t v_bi_boxed_540_; uint8_t v_kind_boxed_541_; lean_object* v_res_542_; 
v_bi_boxed_540_ = lean_unbox(v_bi_531_);
v_kind_boxed_541_ = lean_unbox(v_kind_534_);
v_res_542_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_530_, v_bi_boxed_540_, v_type_532_, v_k_533_, v_kind_boxed_541_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(lean_object* v_name_543_, lean_object* v_type_544_, lean_object* v_k_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
uint8_t v___x_551_; uint8_t v___x_552_; lean_object* v___x_553_; 
v___x_551_ = 0;
v___x_552_ = 0;
v___x_553_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_543_, v___x_551_, v_type_544_, v_k_545_, v___x_552_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg___boxed(lean_object* v_name_554_, lean_object* v_type_555_, lean_object* v_k_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_554_, v_type_555_, v_k_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_562_;
}
}
static lean_object* _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2));
v___x_567_ = lean_unsigned_to_nat(8u);
v___x_568_ = lean_unsigned_to_nat(91u);
v___x_569_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1));
v___x_570_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0));
v___x_571_ = l_mkPanicMessageWithDecl(v___x_570_, v___x_569_, v___x_568_, v___x_567_, v___x_566_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed(lean_object* v_zs2_572_, lean_object* v_acc_573_, lean_object* v_ctor_574_, lean_object* v_k_575_, lean_object* v_zs_576_, lean_object* v_indices_577_, lean_object* v_tail_578_, lean_object* v_tail_579_, lean_object* v_z_x27_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0(v_zs2_572_, v_acc_573_, v_ctor_574_, v_k_575_, v_zs_576_, v_indices_577_, v_tail_578_, v_tail_579_, v_z_x27_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(lean_object* v_ctor_588_, lean_object* v_k_589_, lean_object* v_zs_590_, lean_object* v_indices_591_, lean_object* v_zs2_592_, lean_object* v_mask_593_, lean_object* v_todo_594_, lean_object* v_acc_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
if (lean_obj_tag(v_mask_593_) == 1)
{
lean_object* v_head_601_; uint8_t v___x_602_; 
v_head_601_ = lean_ctor_get(v_mask_593_, 0);
v___x_602_ = lean_unbox(v_head_601_);
if (v___x_602_ == 0)
{
if (lean_obj_tag(v_todo_594_) == 1)
{
lean_object* v_tail_603_; lean_object* v_tail_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_tail_603_ = lean_ctor_get(v_mask_593_, 1);
lean_inc(v_tail_603_);
lean_dec_ref(v_mask_593_);
v_tail_604_ = lean_ctor_get(v_todo_594_, 1);
lean_inc(v_tail_604_);
lean_dec_ref(v_todo_594_);
lean_inc_ref(v_ctor_588_);
v___x_605_ = l_Lean_mkAppN(v_ctor_588_, v_zs2_592_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
v___x_606_ = lean_infer_type(v___x_605_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref(v___x_606_);
v___x_608_ = l_Lean_Meta_whnfForall(v_a_607_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; uint8_t v___x_610_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref(v___x_608_);
v___x_610_ = l_Lean_Expr_isForall(v_a_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec(v_a_609_);
lean_dec(v_tail_604_);
lean_dec(v_tail_603_);
lean_dec_ref(v_acc_595_);
lean_dec_ref(v_zs2_592_);
lean_dec_ref(v_indices_591_);
lean_dec_ref(v_zs_590_);
lean_dec_ref(v_k_589_);
lean_dec_ref(v_ctor_588_);
v___x_611_ = lean_obj_once(&l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3, &l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3_once, _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3);
v___x_612_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v___x_611_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
return v___x_612_;
}
else
{
lean_object* v___f_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___f_613_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_613_, 0, v_zs2_592_);
lean_closure_set(v___f_613_, 1, v_acc_595_);
lean_closure_set(v___f_613_, 2, v_ctor_588_);
lean_closure_set(v___f_613_, 3, v_k_589_);
lean_closure_set(v___f_613_, 4, v_zs_590_);
lean_closure_set(v___f_613_, 5, v_indices_591_);
lean_closure_set(v___f_613_, 6, v_tail_603_);
lean_closure_set(v___f_613_, 7, v_tail_604_);
v___x_614_ = l_Lean_Expr_bindingName_x21(v_a_609_);
v___x_615_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4));
v___x_616_ = lean_name_append_after(v___x_614_, v___x_615_);
v___x_617_ = l_Lean_Expr_bindingDomain_x21(v_a_609_);
lean_dec(v_a_609_);
v___x_618_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v___x_616_, v___x_617_, v___f_613_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
return v___x_618_;
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_tail_604_);
lean_dec(v_tail_603_);
lean_dec_ref(v_acc_595_);
lean_dec_ref(v_zs2_592_);
lean_dec_ref(v_indices_591_);
lean_dec_ref(v_zs_590_);
lean_dec_ref(v_k_589_);
lean_dec_ref(v_ctor_588_);
v_a_619_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_608_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_608_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_tail_604_);
lean_dec(v_tail_603_);
lean_dec_ref(v_acc_595_);
lean_dec_ref(v_zs2_592_);
lean_dec_ref(v_indices_591_);
lean_dec_ref(v_zs_590_);
lean_dec_ref(v_k_589_);
lean_dec_ref(v_ctor_588_);
v_a_627_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_606_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_606_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v_mask_593_);
lean_dec(v_todo_594_);
lean_dec_ref(v_ctor_588_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
v___x_635_ = lean_apply_9(v_k_589_, v_acc_595_, v_indices_591_, v_zs_590_, v_zs2_592_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
return v___x_635_;
}
}
else
{
if (lean_obj_tag(v_todo_594_) == 1)
{
lean_object* v_tail_636_; lean_object* v_head_637_; lean_object* v_tail_638_; lean_object* v___x_639_; 
v_tail_636_ = lean_ctor_get(v_mask_593_, 1);
lean_inc(v_tail_636_);
lean_dec_ref(v_mask_593_);
v_head_637_ = lean_ctor_get(v_todo_594_, 0);
lean_inc(v_head_637_);
v_tail_638_ = lean_ctor_get(v_todo_594_, 1);
lean_inc(v_tail_638_);
lean_dec_ref(v_todo_594_);
v___x_639_ = lean_array_push(v_zs2_592_, v_head_637_);
v_zs2_592_ = v___x_639_;
v_mask_593_ = v_tail_636_;
v_todo_594_ = v_tail_638_;
goto _start;
}
else
{
lean_object* v___x_641_; 
lean_dec_ref(v_mask_593_);
lean_dec(v_todo_594_);
lean_dec_ref(v_ctor_588_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
v___x_641_ = lean_apply_9(v_k_589_, v_acc_595_, v_indices_591_, v_zs_590_, v_zs2_592_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
return v___x_641_;
}
}
}
else
{
lean_object* v___x_642_; 
lean_dec(v_todo_594_);
lean_dec(v_mask_593_);
lean_dec_ref(v_ctor_588_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
v___x_642_ = lean_apply_9(v_k_589_, v_acc_595_, v_indices_591_, v_zs_590_, v_zs2_592_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0(lean_object* v_zs2_643_, lean_object* v_acc_644_, lean_object* v_ctor_645_, lean_object* v_k_646_, lean_object* v_zs_647_, lean_object* v_indices_648_, lean_object* v_tail_649_, lean_object* v_tail_650_, lean_object* v_z_x27_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_inc_ref(v_z_x27_651_);
v___x_657_ = lean_array_push(v_zs2_643_, v_z_x27_651_);
v___x_658_ = lean_array_push(v_acc_644_, v_z_x27_651_);
v___x_659_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_645_, v_k_646_, v_zs_647_, v_indices_648_, v___x_657_, v_tail_649_, v_tail_650_, v___x_658_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___boxed(lean_object* v_ctor_660_, lean_object* v_k_661_, lean_object* v_zs_662_, lean_object* v_indices_663_, lean_object* v_zs2_664_, lean_object* v_mask_665_, lean_object* v_todo_666_, lean_object* v_acc_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_660_, v_k_661_, v_zs_662_, v_indices_663_, v_zs2_664_, v_mask_665_, v_todo_666_, v_acc_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(lean_object* v_00_u03b1_674_, lean_object* v_ctor_675_, lean_object* v_k_676_, lean_object* v_zs_677_, lean_object* v_indices_678_, lean_object* v_zs2_679_, lean_object* v_mask_680_, lean_object* v_todo_681_, lean_object* v_acc_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_675_, v_k_676_, v_zs_677_, v_indices_678_, v_zs2_679_, v_mask_680_, v_todo_681_, v_acc_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___boxed(lean_object* v_00_u03b1_689_, lean_object* v_ctor_690_, lean_object* v_k_691_, lean_object* v_zs_692_, lean_object* v_indices_693_, lean_object* v_zs2_694_, lean_object* v_mask_695_, lean_object* v_todo_696_, lean_object* v_acc_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(v_00_u03b1_689_, v_ctor_690_, v_k_691_, v_zs_692_, v_indices_693_, v_zs2_694_, v_mask_695_, v_todo_696_, v_acc_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(lean_object* v_00_u03b1_704_, lean_object* v_name_705_, uint8_t v_bi_706_, lean_object* v_type_707_, lean_object* v_k_708_, uint8_t v_kind_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_705_, v_bi_706_, v_type_707_, v_k_708_, v_kind_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___boxed(lean_object* v_00_u03b1_716_, lean_object* v_name_717_, lean_object* v_bi_718_, lean_object* v_type_719_, lean_object* v_k_720_, lean_object* v_kind_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
uint8_t v_bi_boxed_727_; uint8_t v_kind_boxed_728_; lean_object* v_res_729_; 
v_bi_boxed_727_ = lean_unbox(v_bi_718_);
v_kind_boxed_728_ = lean_unbox(v_kind_721_);
v_res_729_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(v_00_u03b1_716_, v_name_717_, v_bi_boxed_727_, v_type_719_, v_k_720_, v_kind_boxed_728_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(lean_object* v_00_u03b1_730_, lean_object* v_name_731_, lean_object* v_type_732_, lean_object* v_k_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_731_, v_type_732_, v_k_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___boxed(lean_object* v_00_u03b1_740_, lean_object* v_name_741_, lean_object* v_type_742_, lean_object* v_k_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(v_00_u03b1_740_, v_name_741_, v_type_742_, v_k_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(lean_object* v_type_750_, lean_object* v_k_751_, uint8_t v_cleanupAnnotations_752_, uint8_t v_whnfType_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___f_759_; lean_object* v___x_760_; 
v___f_759_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_759_, 0, v_k_751_);
v___x_760_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_750_, v___f_759_, v_cleanupAnnotations_752_, v_whnfType_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
v_a_769_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_760_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_760_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg___boxed(lean_object* v_type_777_, lean_object* v_k_778_, lean_object* v_cleanupAnnotations_779_, lean_object* v_whnfType_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_786_; uint8_t v_whnfType_boxed_787_; lean_object* v_res_788_; 
v_cleanupAnnotations_boxed_786_ = lean_unbox(v_cleanupAnnotations_779_);
v_whnfType_boxed_787_ = lean_unbox(v_whnfType_780_);
v_res_788_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_777_, v_k_778_, v_cleanupAnnotations_boxed_786_, v_whnfType_boxed_787_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(lean_object* v_00_u03b1_789_, lean_object* v_type_790_, lean_object* v_k_791_, uint8_t v_cleanupAnnotations_792_, uint8_t v_whnfType_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_790_, v_k_791_, v_cleanupAnnotations_792_, v_whnfType_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___boxed(lean_object* v_00_u03b1_800_, lean_object* v_type_801_, lean_object* v_k_802_, lean_object* v_cleanupAnnotations_803_, lean_object* v_whnfType_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_810_; uint8_t v_whnfType_boxed_811_; lean_object* v_res_812_; 
v_cleanupAnnotations_boxed_810_ = lean_unbox(v_cleanupAnnotations_803_);
v_whnfType_boxed_811_ = lean_unbox(v_whnfType_804_);
v_res_812_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(v_00_u03b1_800_, v_type_801_, v_k_802_, v_cleanupAnnotations_boxed_810_, v_whnfType_boxed_811_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v_res_812_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(lean_object* v_constName_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; lean_object* v_env_823_; lean_object* v___x_824_; 
v___x_822_ = lean_st_ref_get(v___y_820_);
v_env_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc_ref(v_env_823_);
lean_dec(v___x_822_);
lean_inc(v_constName_816_);
v___x_824_ = l_Lean_isInductiveCore_x3f(v_env_823_, v_constName_816_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_825_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
v___x_826_ = 0;
v___x_827_ = l_Lean_MessageData_ofConstName(v_constName_816_, v___x_826_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_825_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_830_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
return v___x_831_;
}
else
{
lean_object* v_val_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_constName_816_);
v_val_832_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_824_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_val_832_);
lean_dec(v___x_824_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 0);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_val_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___boxed(lean_object* v_constName_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(v_constName_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
return v_res_846_;
}
}
static lean_object* _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_847_; lean_object* v_dummy_848_; 
v___x_847_ = lean_box(0);
v_dummy_848_ = l_Lean_Expr_sort___override(v___x_847_);
return v_dummy_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(lean_object* v_ctor_851_, lean_object* v_k_852_, lean_object* v_zs_853_, lean_object* v_ctorRet_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
v___x_860_ = lean_whnf(v_ctorRet_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref(v___x_860_);
v___x_862_ = l_Lean_Core_betaReduce(v_a_861_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_862_);
v___x_864_ = l_Lean_Expr_getAppFn(v_a_863_);
v___x_865_ = l_Lean_Expr_constName_x21(v___x_864_);
lean_dec_ref(v___x_864_);
v___x_866_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(v___x_865_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v_numIndices_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
v_numIndices_868_ = lean_ctor_get(v_a_867_, 2);
lean_inc(v_numIndices_868_);
lean_dec(v_a_867_);
v___x_869_ = l_Lean_Expr_getAppFn(v_ctor_851_);
v___x_870_ = l_Lean_Expr_constName_x21(v___x_869_);
lean_dec_ref(v___x_869_);
v___x_871_ = l_Lean_Meta_occursInCtorTypeMask(v___x_870_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v_dummy_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref(v___x_871_);
v_dummy_873_ = lean_obj_once(&l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0, &l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0);
lean_inc(v_numIndices_868_);
v___x_874_ = lean_mk_array(v_numIndices_868_, v_dummy_873_);
v___x_875_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numIndices_868_, v_a_863_, v___x_874_);
v___x_876_ = ((lean_object*)(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1));
v___x_877_ = lean_array_to_list(v_a_872_);
lean_inc_ref(v_zs_853_);
v___x_878_ = lean_array_to_list(v_zs_853_);
lean_inc_ref(v_zs_853_);
v___x_879_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_851_, v_k_852_, v_zs_853_, v___x_875_, v___x_876_, v___x_877_, v___x_878_, v_zs_853_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
return v___x_879_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_numIndices_868_);
lean_dec(v_a_863_);
lean_dec_ref(v_zs_853_);
lean_dec_ref(v_k_852_);
lean_dec_ref(v_ctor_851_);
v_a_880_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_871_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_871_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_a_863_);
lean_dec_ref(v_zs_853_);
lean_dec_ref(v_k_852_);
lean_dec_ref(v_ctor_851_);
v_a_888_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_866_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_866_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v_zs_853_);
lean_dec_ref(v_k_852_);
lean_dec_ref(v_ctor_851_);
v_a_896_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_862_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_862_);
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
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref(v_zs_853_);
lean_dec_ref(v_k_852_);
lean_dec_ref(v_ctor_851_);
v_a_904_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_860_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_860_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed(lean_object* v_ctor_912_, lean_object* v_k_913_, lean_object* v_zs_914_, lean_object* v_ctorRet_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(v_ctor_912_, v_k_913_, v_zs_914_, v_ctorRet_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg(lean_object* v_ctor_922_, lean_object* v_k_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_929_; 
lean_inc(v_a_927_);
lean_inc_ref(v_a_926_);
lean_inc(v_a_925_);
lean_inc_ref(v_a_924_);
lean_inc_ref(v_ctor_922_);
v___x_929_ = lean_infer_type(v_ctor_922_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___f_931_; uint8_t v___x_932_; lean_object* v___x_933_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref(v___x_929_);
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_931_, 0, v_ctor_922_);
lean_closure_set(v___f_931_, 1, v_k_923_);
v___x_932_ = 0;
v___x_933_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_a_930_, v___f_931_, v___x_932_, v___x_932_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
return v___x_933_;
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v_k_923_);
lean_dec_ref(v_ctor_922_);
v_a_934_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_929_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_929_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___boxed(lean_object* v_ctor_942_, lean_object* v_k_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Meta_withSharedCtorIndices___redArg(v_ctor_942_, v_k_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices(lean_object* v_00_u03b1_950_, lean_object* v_ctor_951_, lean_object* v_k_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Meta_withSharedCtorIndices___redArg(v_ctor_951_, v_k_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___boxed(lean_object* v_00_u03b1_959_, lean_object* v_ctor_960_, lean_object* v_k_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Meta_withSharedCtorIndices(v_00_u03b1_959_, v_ctor_960_, v_k_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
return v_res_967_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_SameCtorUtils(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_SameCtorUtils(builtin);
}
#ifdef __cplusplus
}
#endif
