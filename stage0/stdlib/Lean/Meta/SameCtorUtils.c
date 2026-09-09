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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_5_, 1);
v___x_7_ = lean_expr_eqv(v_s_3_, v_e_2_);
lean_dec_ref_known(v_s_3_, 1);
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
lean_dec_ref_known(v_s_3_, 1);
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
lean_dec_ref_known(v___x_21_, 1);
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
lean_dec_ref_known(v___x_144_, 1);
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
v_sz_152_ = lean_array_size(v_ys_137_);
v___x_153_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_151_);
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
lean_dec_ref(v___y_177_);
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
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_2054__overap_267_; lean_object* v___x_268_; 
v___x_265_ = lean_box(0);
v___x_266_ = l_instInhabitedOfMonad___redArg(v___x_264_, v___x_265_);
v___x_2054__overap_267_ = lean_panic_fn_borrowed(v___x_266_, v_msg_210_);
lean_dec(v___x_266_);
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
lean_inc(v___y_212_);
lean_inc_ref(v___y_211_);
v___x_268_ = lean_apply_5(v___x_2054__overap_267_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, lean_box(0));
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
lean_object* v___x_294_; lean_object* v_env_295_; lean_object* v___x_296_; lean_object* v_toCold_297_; lean_object* v_mctx_298_; lean_object* v_lctx_299_; lean_object* v_options_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_294_ = lean_st_ref_get(v___y_292_);
v_env_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc_ref(v_env_295_);
lean_dec(v___x_294_);
v___x_296_ = lean_st_ref_get(v___y_290_);
v_toCold_297_ = lean_ctor_get(v___y_291_, 0);
v_mctx_298_ = lean_ctor_get(v___x_296_, 0);
lean_inc_ref(v_mctx_298_);
lean_dec(v___x_296_);
v_lctx_299_ = lean_ctor_get(v___y_289_, 2);
v_options_300_ = lean_ctor_get(v_toCold_297_, 2);
lean_inc_ref(v_options_300_);
lean_inc_ref(v_lctx_299_);
v___x_301_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_301_, 0, v_env_295_);
lean_ctor_set(v___x_301_, 1, v_mctx_298_);
lean_ctor_set(v___x_301_, 2, v_lctx_299_);
lean_ctor_set(v___x_301_, 3, v_options_300_);
v___x_302_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v_msgData_288_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msgData_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(lean_object* v_msg_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_ref_317_; lean_object* v___x_318_; lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_327_; 
v_ref_317_ = lean_ctor_get(v___y_314_, 2);
v___x_318_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msg_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_327_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
lean_inc(v_ref_317_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v_ref_317_);
lean_ctor_set(v___x_323_, 1, v_a_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 1);
lean_ctor_set(v___x_321_, 0, v___x_323_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg___boxed(lean_object* v_msg_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0));
v___x_337_ = l_Lean_stringToMessageData(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2));
v___x_340_ = l_Lean_stringToMessageData(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_344_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6));
v___x_345_ = lean_unsigned_to_nat(11u);
v___x_346_ = lean_unsigned_to_nat(122u);
v___x_347_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5));
v___x_348_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4));
v___x_349_ = l_mkPanicMessageWithDecl(v___x_348_, v___x_347_, v___x_346_, v___x_345_, v___x_344_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(lean_object* v_constName_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_364_; lean_object* v_env_365_; uint8_t v___x_366_; lean_object* v___x_367_; 
v___x_364_ = lean_st_ref_get(v___y_354_);
v_env_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_env_365_);
lean_dec(v___x_364_);
v___x_366_ = 0;
lean_inc(v_constName_350_);
v___x_367_ = l_Lean_Environment_findAsync_x3f(v_env_365_, v_constName_350_, v___x_366_);
if (lean_obj_tag(v___x_367_) == 1)
{
lean_object* v_val_368_; uint8_t v_kind_369_; 
v_val_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_val_368_);
lean_dec_ref_known(v___x_367_, 1);
v_kind_369_ = lean_ctor_get_uint8(v_val_368_, sizeof(void*)*3);
if (v_kind_369_ == 6)
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_368_);
if (lean_obj_tag(v___x_370_) == 6)
{
lean_object* v_val_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_constName_350_);
v_val_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_val_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set_tag(v___x_373_, 0);
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_val_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec_ref(v___x_370_);
v___x_379_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7);
v___x_380_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v___x_379_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_389_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_389_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
if (lean_obj_tag(v_a_381_) == 0)
{
lean_del_object(v___x_383_);
goto v___jp_356_;
}
else
{
lean_object* v_val_385_; lean_object* v___x_387_; 
lean_dec(v_constName_350_);
v_val_385_ = lean_ctor_get(v_a_381_, 0);
lean_inc(v_val_385_);
lean_dec_ref_known(v_a_381_, 1);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v_val_385_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_val_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v_constName_350_);
v_a_390_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_380_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_380_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
else
{
lean_dec(v_val_368_);
goto v___jp_356_;
}
}
else
{
lean_dec(v___x_367_);
goto v___jp_356_;
}
v___jp_356_:
{
lean_object* v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_357_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
v___x_358_ = 0;
v___x_359_ = l_Lean_MessageData_ofConstName(v_constName_350_, v___x_358_);
v___x_360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_357_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3);
v___x_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_362_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___boxed(lean_object* v_constName_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(v_constName_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask(lean_object* v_ctorName_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(v_ctorName_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v_toConstantVal_414_; lean_object* v_numParams_415_; lean_object* v_numFields_416_; lean_object* v_type_417_; lean_object* v___f_418_; lean_object* v___f_419_; lean_object* v___x_420_; uint8_t v___x_421_; lean_object* v___x_422_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v_toConstantVal_414_ = lean_ctor_get(v_a_413_, 0);
lean_inc_ref(v_toConstantVal_414_);
v_numParams_415_ = lean_ctor_get(v_a_413_, 3);
lean_inc(v_numParams_415_);
v_numFields_416_ = lean_ctor_get(v_a_413_, 4);
lean_inc(v_numFields_416_);
lean_dec(v_a_413_);
v_type_417_ = lean_ctor_get(v_toConstantVal_414_, 2);
lean_inc_ref(v_type_417_);
lean_dec_ref(v_toConstantVal_414_);
v___f_418_ = ((lean_object*)(l_Lean_Meta_occursInCtorTypeMask___closed__0));
v___f_419_ = lean_alloc_closure((void*)(l_Lean_Meta_occursInCtorTypeMask___lam__1___boxed), 9, 2);
lean_closure_set(v___f_419_, 0, v_numFields_416_);
lean_closure_set(v___f_419_, 1, v___f_418_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v_numParams_415_);
v___x_421_ = 0;
v___x_422_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_type_417_, v___x_420_, v___f_419_, v___x_421_, v___x_421_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
return v___x_422_;
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
v_a_423_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_412_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_412_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___boxed(lean_object* v_ctorName_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_occursInCtorTypeMask(v_ctorName_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(lean_object* v_00_u03b1_438_, lean_object* v_msg_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___boxed(lean_object* v_00_u03b1_446_, lean_object* v_msg_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(v_00_u03b1_446_, v_msg_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(lean_object* v_msg_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___f_461_; lean_object* v___x_536__overap_462_; lean_object* v___x_463_; 
v___f_461_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0));
v___x_536__overap_462_ = lean_panic_fn_borrowed(v___f_461_, v_msg_455_);
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
lean_inc(v___y_457_);
lean_inc_ref(v___y_456_);
v___x_463_ = lean_apply_5(v___x_536__overap_462_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, lean_box(0));
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___boxed(lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(lean_object* v_00_u03b1_471_, lean_object* v_msg_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___boxed(lean_object* v_00_u03b1_479_, lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(v_00_u03b1_479_, v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(lean_object* v_k_487_, lean_object* v_b_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; 
lean_inc(v___y_492_);
lean_inc_ref(v___y_491_);
lean_inc(v___y_490_);
lean_inc_ref(v___y_489_);
v___x_494_ = lean_apply_6(v_k_487_, v_b_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, lean_box(0));
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_495_, lean_object* v_b_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(v_k_495_, v_b_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(lean_object* v_name_503_, uint8_t v_bi_504_, lean_object* v_type_505_, lean_object* v_k_506_, uint8_t v_kind_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___f_513_; lean_object* v___x_514_; 
v___f_513_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_513_, 0, v_k_506_);
v___x_514_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_503_, v_bi_504_, v_type_505_, v___f_513_, v_kind_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_a_523_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_514_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_514_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___boxed(lean_object* v_name_531_, lean_object* v_bi_532_, lean_object* v_type_533_, lean_object* v_k_534_, lean_object* v_kind_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v_bi_boxed_541_; uint8_t v_kind_boxed_542_; lean_object* v_res_543_; 
v_bi_boxed_541_ = lean_unbox(v_bi_532_);
v_kind_boxed_542_ = lean_unbox(v_kind_535_);
v_res_543_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_531_, v_bi_boxed_541_, v_type_533_, v_k_534_, v_kind_boxed_542_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(lean_object* v_name_544_, lean_object* v_type_545_, lean_object* v_k_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
uint8_t v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = 0;
v___x_553_ = 0;
v___x_554_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_544_, v___x_552_, v_type_545_, v_k_546_, v___x_553_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg___boxed(lean_object* v_name_555_, lean_object* v_type_556_, lean_object* v_k_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_555_, v_type_556_, v_k_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_563_;
}
}
static lean_object* _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_567_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2));
v___x_568_ = lean_unsigned_to_nat(8u);
v___x_569_ = lean_unsigned_to_nat(91u);
v___x_570_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1));
v___x_571_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0));
v___x_572_ = l_mkPanicMessageWithDecl(v___x_571_, v___x_570_, v___x_569_, v___x_568_, v___x_567_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed(lean_object* v_zs2_573_, lean_object* v_acc_574_, lean_object* v_ctor_575_, lean_object* v_k_576_, lean_object* v_zs_577_, lean_object* v_indices_578_, lean_object* v_tail_579_, lean_object* v_tail_580_, lean_object* v_z_x27_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0(v_zs2_573_, v_acc_574_, v_ctor_575_, v_k_576_, v_zs_577_, v_indices_578_, v_tail_579_, v_tail_580_, v_z_x27_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(lean_object* v_ctor_589_, lean_object* v_k_590_, lean_object* v_zs_591_, lean_object* v_indices_592_, lean_object* v_zs2_593_, lean_object* v_mask_594_, lean_object* v_todo_595_, lean_object* v_acc_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
if (lean_obj_tag(v_mask_594_) == 1)
{
lean_object* v_head_602_; uint8_t v___x_603_; 
v_head_602_ = lean_ctor_get(v_mask_594_, 0);
v___x_603_ = lean_unbox(v_head_602_);
if (v___x_603_ == 0)
{
if (lean_obj_tag(v_todo_595_) == 1)
{
lean_object* v_tail_604_; lean_object* v_tail_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_tail_604_ = lean_ctor_get(v_mask_594_, 1);
lean_inc(v_tail_604_);
lean_dec_ref_known(v_mask_594_, 2);
v_tail_605_ = lean_ctor_get(v_todo_595_, 1);
lean_inc(v_tail_605_);
lean_dec_ref_known(v_todo_595_, 2);
lean_inc_ref(v_ctor_589_);
v___x_606_ = l_Lean_mkAppN(v_ctor_589_, v_zs2_593_);
lean_inc(v_a_600_);
lean_inc_ref(v_a_599_);
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
v___x_607_ = lean_infer_type(v___x_606_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = l_Lean_Meta_whnfForall(v_a_608_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; uint8_t v___x_611_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
v___x_611_ = l_Lean_Expr_isForall(v_a_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v_a_610_);
lean_dec(v_tail_605_);
lean_dec(v_tail_604_);
lean_dec_ref(v_acc_596_);
lean_dec_ref(v_zs2_593_);
lean_dec_ref(v_indices_592_);
lean_dec_ref(v_zs_591_);
lean_dec_ref(v_k_590_);
lean_dec_ref(v_ctor_589_);
v___x_612_ = lean_obj_once(&l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3, &l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3_once, _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3);
v___x_613_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v___x_612_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
return v___x_613_;
}
else
{
lean_object* v___f_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___f_614_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_614_, 0, v_zs2_593_);
lean_closure_set(v___f_614_, 1, v_acc_596_);
lean_closure_set(v___f_614_, 2, v_ctor_589_);
lean_closure_set(v___f_614_, 3, v_k_590_);
lean_closure_set(v___f_614_, 4, v_zs_591_);
lean_closure_set(v___f_614_, 5, v_indices_592_);
lean_closure_set(v___f_614_, 6, v_tail_604_);
lean_closure_set(v___f_614_, 7, v_tail_605_);
v___x_615_ = l_Lean_Expr_bindingName_x21(v_a_610_);
v___x_616_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4));
v___x_617_ = lean_name_append_after(v___x_615_, v___x_616_);
v___x_618_ = l_Lean_Expr_bindingDomain_x21(v_a_610_);
lean_dec(v_a_610_);
v___x_619_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v___x_617_, v___x_618_, v___f_614_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
return v___x_619_;
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_tail_605_);
lean_dec(v_tail_604_);
lean_dec_ref(v_acc_596_);
lean_dec_ref(v_zs2_593_);
lean_dec_ref(v_indices_592_);
lean_dec_ref(v_zs_591_);
lean_dec_ref(v_k_590_);
lean_dec_ref(v_ctor_589_);
v_a_620_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_609_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_609_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v_tail_605_);
lean_dec(v_tail_604_);
lean_dec_ref(v_acc_596_);
lean_dec_ref(v_zs2_593_);
lean_dec_ref(v_indices_592_);
lean_dec_ref(v_zs_591_);
lean_dec_ref(v_k_590_);
lean_dec_ref(v_ctor_589_);
v_a_628_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_607_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_607_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v___x_636_; 
lean_dec_ref_known(v_mask_594_, 2);
lean_dec(v_todo_595_);
lean_dec_ref(v_ctor_589_);
lean_inc(v_a_600_);
lean_inc_ref(v_a_599_);
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
v___x_636_ = lean_apply_9(v_k_590_, v_acc_596_, v_indices_592_, v_zs_591_, v_zs2_593_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, lean_box(0));
return v___x_636_;
}
}
else
{
if (lean_obj_tag(v_todo_595_) == 1)
{
lean_object* v_tail_637_; lean_object* v_head_638_; lean_object* v_tail_639_; lean_object* v___x_640_; 
v_tail_637_ = lean_ctor_get(v_mask_594_, 1);
lean_inc(v_tail_637_);
lean_dec_ref_known(v_mask_594_, 2);
v_head_638_ = lean_ctor_get(v_todo_595_, 0);
lean_inc(v_head_638_);
v_tail_639_ = lean_ctor_get(v_todo_595_, 1);
lean_inc(v_tail_639_);
lean_dec_ref_known(v_todo_595_, 2);
v___x_640_ = lean_array_push(v_zs2_593_, v_head_638_);
v_zs2_593_ = v___x_640_;
v_mask_594_ = v_tail_637_;
v_todo_595_ = v_tail_639_;
goto _start;
}
else
{
lean_object* v___x_642_; 
lean_dec_ref_known(v_mask_594_, 2);
lean_dec(v_todo_595_);
lean_dec_ref(v_ctor_589_);
lean_inc(v_a_600_);
lean_inc_ref(v_a_599_);
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
v___x_642_ = lean_apply_9(v_k_590_, v_acc_596_, v_indices_592_, v_zs_591_, v_zs2_593_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, lean_box(0));
return v___x_642_;
}
}
}
else
{
lean_object* v___x_643_; 
lean_dec(v_todo_595_);
lean_dec(v_mask_594_);
lean_dec_ref(v_ctor_589_);
lean_inc(v_a_600_);
lean_inc_ref(v_a_599_);
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
v___x_643_ = lean_apply_9(v_k_590_, v_acc_596_, v_indices_592_, v_zs_591_, v_zs2_593_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, lean_box(0));
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0(lean_object* v_zs2_644_, lean_object* v_acc_645_, lean_object* v_ctor_646_, lean_object* v_k_647_, lean_object* v_zs_648_, lean_object* v_indices_649_, lean_object* v_tail_650_, lean_object* v_tail_651_, lean_object* v_z_x27_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_inc_ref(v_z_x27_652_);
v___x_658_ = lean_array_push(v_zs2_644_, v_z_x27_652_);
v___x_659_ = lean_array_push(v_acc_645_, v_z_x27_652_);
v___x_660_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_646_, v_k_647_, v_zs_648_, v_indices_649_, v___x_658_, v_tail_650_, v_tail_651_, v___x_659_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___boxed(lean_object* v_ctor_661_, lean_object* v_k_662_, lean_object* v_zs_663_, lean_object* v_indices_664_, lean_object* v_zs2_665_, lean_object* v_mask_666_, lean_object* v_todo_667_, lean_object* v_acc_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_661_, v_k_662_, v_zs_663_, v_indices_664_, v_zs2_665_, v_mask_666_, v_todo_667_, v_acc_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(lean_object* v_00_u03b1_675_, lean_object* v_ctor_676_, lean_object* v_k_677_, lean_object* v_zs_678_, lean_object* v_indices_679_, lean_object* v_zs2_680_, lean_object* v_mask_681_, lean_object* v_todo_682_, lean_object* v_acc_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_676_, v_k_677_, v_zs_678_, v_indices_679_, v_zs2_680_, v_mask_681_, v_todo_682_, v_acc_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___boxed(lean_object* v_00_u03b1_690_, lean_object* v_ctor_691_, lean_object* v_k_692_, lean_object* v_zs_693_, lean_object* v_indices_694_, lean_object* v_zs2_695_, lean_object* v_mask_696_, lean_object* v_todo_697_, lean_object* v_acc_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(v_00_u03b1_690_, v_ctor_691_, v_k_692_, v_zs_693_, v_indices_694_, v_zs2_695_, v_mask_696_, v_todo_697_, v_acc_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(lean_object* v_00_u03b1_705_, lean_object* v_name_706_, uint8_t v_bi_707_, lean_object* v_type_708_, lean_object* v_k_709_, uint8_t v_kind_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_706_, v_bi_707_, v_type_708_, v_k_709_, v_kind_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___boxed(lean_object* v_00_u03b1_717_, lean_object* v_name_718_, lean_object* v_bi_719_, lean_object* v_type_720_, lean_object* v_k_721_, lean_object* v_kind_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
uint8_t v_bi_boxed_728_; uint8_t v_kind_boxed_729_; lean_object* v_res_730_; 
v_bi_boxed_728_ = lean_unbox(v_bi_719_);
v_kind_boxed_729_ = lean_unbox(v_kind_722_);
v_res_730_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(v_00_u03b1_717_, v_name_718_, v_bi_boxed_728_, v_type_720_, v_k_721_, v_kind_boxed_729_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(lean_object* v_00_u03b1_731_, lean_object* v_name_732_, lean_object* v_type_733_, lean_object* v_k_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_732_, v_type_733_, v_k_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___boxed(lean_object* v_00_u03b1_741_, lean_object* v_name_742_, lean_object* v_type_743_, lean_object* v_k_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(v_00_u03b1_741_, v_name_742_, v_type_743_, v_k_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(lean_object* v_type_751_, lean_object* v_k_752_, uint8_t v_cleanupAnnotations_753_, uint8_t v_whnfType_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___f_760_; lean_object* v___x_761_; 
v___f_760_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_760_, 0, v_k_752_);
v___x_761_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_751_, v___f_760_, v_cleanupAnnotations_753_, v_whnfType_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
v_a_770_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_761_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_761_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg___boxed(lean_object* v_type_778_, lean_object* v_k_779_, lean_object* v_cleanupAnnotations_780_, lean_object* v_whnfType_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_787_; uint8_t v_whnfType_boxed_788_; lean_object* v_res_789_; 
v_cleanupAnnotations_boxed_787_ = lean_unbox(v_cleanupAnnotations_780_);
v_whnfType_boxed_788_ = lean_unbox(v_whnfType_781_);
v_res_789_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_778_, v_k_779_, v_cleanupAnnotations_boxed_787_, v_whnfType_boxed_788_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(lean_object* v_00_u03b1_790_, lean_object* v_type_791_, lean_object* v_k_792_, uint8_t v_cleanupAnnotations_793_, uint8_t v_whnfType_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_791_, v_k_792_, v_cleanupAnnotations_793_, v_whnfType_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___boxed(lean_object* v_00_u03b1_801_, lean_object* v_type_802_, lean_object* v_k_803_, lean_object* v_cleanupAnnotations_804_, lean_object* v_whnfType_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_811_; uint8_t v_whnfType_boxed_812_; lean_object* v_res_813_; 
v_cleanupAnnotations_boxed_811_ = lean_unbox(v_cleanupAnnotations_804_);
v_whnfType_boxed_812_ = lean_unbox(v_whnfType_805_);
v_res_813_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(v_00_u03b1_801_, v_type_802_, v_k_803_, v_cleanupAnnotations_boxed_811_, v_whnfType_boxed_812_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_813_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0));
v___x_816_ = l_Lean_stringToMessageData(v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(lean_object* v_constName_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; lean_object* v_env_824_; lean_object* v___x_825_; 
v___x_823_ = lean_st_ref_get(v___y_821_);
v_env_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc_ref(v_env_824_);
lean_dec(v___x_823_);
lean_inc(v_constName_817_);
v___x_825_ = l_Lean_isInductiveCore_x3f(v_env_824_, v_constName_817_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_826_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
v___x_827_ = 0;
v___x_828_ = l_Lean_MessageData_ofConstName(v_constName_817_, v___x_827_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_826_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_831_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
return v___x_832_;
}
else
{
lean_object* v_val_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_constName_817_);
v_val_833_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_825_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_val_833_);
lean_dec(v___x_825_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 0);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_val_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___boxed(lean_object* v_constName_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(v_constName_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
static lean_object* _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_848_; lean_object* v_dummy_849_; 
v___x_848_ = lean_box(0);
v_dummy_849_ = l_Lean_Expr_sort___override(v___x_848_);
return v_dummy_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(lean_object* v_ctor_852_, lean_object* v_k_853_, lean_object* v_zs_854_, lean_object* v_ctorRet_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; 
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
v___x_861_ = lean_whnf(v_ctorRet_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
v___x_863_ = l_Lean_Core_betaReduce(v_a_862_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___x_865_ = l_Lean_Expr_getAppFn(v_a_864_);
v___x_866_ = l_Lean_Expr_constName_x21(v___x_865_);
lean_dec_ref(v___x_865_);
v___x_867_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(v___x_866_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v_numIndices_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v_numIndices_869_ = lean_ctor_get(v_a_868_, 2);
lean_inc(v_numIndices_869_);
lean_dec(v_a_868_);
v___x_870_ = l_Lean_Expr_getAppFn(v_ctor_852_);
v___x_871_ = l_Lean_Expr_constName_x21(v___x_870_);
lean_dec_ref(v___x_870_);
v___x_872_ = l_Lean_Meta_occursInCtorTypeMask(v___x_871_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v_dummy_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 1);
v_dummy_874_ = lean_obj_once(&l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0, &l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0);
lean_inc(v_numIndices_869_);
v___x_875_ = lean_mk_array(v_numIndices_869_, v_dummy_874_);
v___x_876_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numIndices_869_, v_a_864_, v___x_875_);
v___x_877_ = ((lean_object*)(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1));
v___x_878_ = lean_array_to_list(v_a_873_);
lean_inc_ref_n(v_zs_854_, 2);
v___x_879_ = lean_array_to_list(v_zs_854_);
v___x_880_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_852_, v_k_853_, v_zs_854_, v___x_876_, v___x_877_, v___x_878_, v___x_879_, v_zs_854_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_880_;
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_numIndices_869_);
lean_dec(v_a_864_);
lean_dec_ref(v_zs_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_ctor_852_);
v_a_881_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_872_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_872_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v_a_864_);
lean_dec_ref(v_zs_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_ctor_852_);
v_a_889_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_867_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_867_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v_zs_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_ctor_852_);
v_a_897_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_863_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_863_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v_zs_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_ctor_852_);
v_a_905_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_861_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_861_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed(lean_object* v_ctor_913_, lean_object* v_k_914_, lean_object* v_zs_915_, lean_object* v_ctorRet_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(v_ctor_913_, v_k_914_, v_zs_915_, v_ctorRet_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg(lean_object* v_ctor_923_, lean_object* v_k_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; 
lean_inc(v_a_928_);
lean_inc_ref(v_a_927_);
lean_inc(v_a_926_);
lean_inc_ref(v_a_925_);
lean_inc_ref(v_ctor_923_);
v___x_930_ = lean_infer_type(v_ctor_923_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___f_932_; uint8_t v___x_933_; lean_object* v___x_934_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v___x_930_, 1);
v___f_932_ = lean_alloc_closure((void*)(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_932_, 0, v_ctor_923_);
lean_closure_set(v___f_932_, 1, v_k_924_);
v___x_933_ = 0;
v___x_934_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_a_931_, v___f_932_, v___x_933_, v___x_933_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
return v___x_934_;
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v_k_924_);
lean_dec_ref(v_ctor_923_);
v_a_935_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_930_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_930_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___boxed(lean_object* v_ctor_943_, lean_object* v_k_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Meta_withSharedCtorIndices___redArg(v_ctor_943_, v_k_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices(lean_object* v_00_u03b1_951_, lean_object* v_ctor_952_, lean_object* v_k_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Meta_withSharedCtorIndices___redArg(v_ctor_952_, v_k_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___boxed(lean_object* v_00_u03b1_960_, lean_object* v_ctor_961_, lean_object* v_k_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Meta_withSharedCtorIndices(v_00_u03b1_960_, v_ctor_961_, v_k_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
return v_res_968_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
