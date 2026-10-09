// Lean compiler output
// Module: Lean.Elab.Deriving.Hashable
// Imports: public import Lean.Meta.Inductive public import Lean.Elab.Deriving.Basic public import Lean.Elab.Deriving.Util
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Hashable"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 184, 111, 151, 29, 127, 247, 194)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mixHash"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(189, 74, 20, 35, 61, 24, 14, 25)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__11_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__13_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__16_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 149, 214, 102, 1, 219, 34, 253)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__23 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__23_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__24_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__26_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__28_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__31_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__32_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__28_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__32_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__33 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__33_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__26_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__33_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__34_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__23_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__34_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hash"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36_value),LEAN_SCALAR_PTR_LITERAL(191, 103, 194, 67, 121, 216, 187, 106)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 184, 111, 151, 29, 127, 247, 194)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36_value),LEAN_SCALAR_PTR_LITERAL(241, 83, 211, 250, 180, 43, 84, 158)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__40 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__40_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__6_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__7_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__0_value;
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__11_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__11_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__12_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "no_expose"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14_value),LEAN_SCALAR_PTR_LITERAL(211, 61, 129, 110, 227, 154, 234, 3)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__16 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__16_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__17_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__18_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__25 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__25_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__31 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28_value),LEAN_SCALAR_PTR_LITERAL(91, 224, 255, 146, 113, 132, 17, 151)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__31_value),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34_value)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44_value),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45_value)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__46 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__46_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "hashable"};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 166, 247, 31, 207, 69, 133, 232)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4;
static const lean_string_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Deriving_Hashable_mkHashableHandler___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHandler___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__0_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Deriving_Hashable_mkHashableHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__0_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__0_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__1_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__1_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__1_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__2_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__1_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__2_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__2_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__2_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 225, 45, 251, 162, 86, 82, 173)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(73, 154, 190, 192, 211, 16, 57, 209)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 19, 134, 125, 143, 124, 44, 190)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 22, 76, 54, 190, 199, 213, 91)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__10_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(108, 133, 113, 226, 183, 145, 134, 17)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__10_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__10_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__11_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__10_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 114, 171, 47, 44, 107, 84, 129)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__11_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__11_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__12_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__12_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__12_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__13_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__11_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__12_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 214, 101, 168, 153, 160, 6, 192)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__13_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__13_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__14_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__14_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__14_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__15_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__13_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__14_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 76, 206, 90, 219, 225, 3, 218)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__15_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__15_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__15_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 168, 84, 49, 33, 100, 57, 131)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(33, 135, 77, 5, 241, 59, 88, 154)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__18_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(119, 51, 149, 107, 14, 108, 122, 130)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__18_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__18_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__19_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__18_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 234, 19, 174, 78, 76, 143, 183)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__19_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__19_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__21_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__21_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__21_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__23_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__23_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__23_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2____boxed(lean_object*);
lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHeader(lean_object* v_indVal_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1));
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = l_Lean_Elab_Deriving_mkHeader(v___x_12_, v___x_13_, v_indVal_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_);
return v___x_14_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Hashable_mkHashableHeader_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_4_ = stack[0].m_obj;
lean_object* v_a_5_ = stack[1].m_obj;
lean_object* v_a_6_ = stack[2].m_obj;
lean_object* v_a_7_ = stack[3].m_obj;
lean_object* v_a_8_ = stack[4].m_obj;
lean_object* v_a_9_ = stack[5].m_obj;
lean_object* v_a_10_ = stack[6].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader(v_indVal_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHeader___boxed(lean_object* v_indVal_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader(v_indVal_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec_ref(v_a_17_);
return v_res_24_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0(lean_object* v_k_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v_b_28_, lean_object* v_c_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; 
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
lean_inc(v___y_31_);
lean_inc_ref(v___y_30_);
lean_inc(v___y_27_);
lean_inc_ref(v___y_26_);
v___x_35_ = lean_apply_9(v_k_25_, v_b_28_, v_c_29_, v___y_26_, v___y_27_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, lean_box(0));
return v___x_35_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_25_ = stack[0].m_obj;
lean_object* v___y_26_ = stack[1].m_obj;
lean_object* v___y_27_ = stack[2].m_obj;
lean_object* v_b_28_ = stack[3].m_obj;
lean_object* v_c_29_ = stack[4].m_obj;
lean_object* v___y_30_ = stack[5].m_obj;
lean_object* v___y_31_ = stack[6].m_obj;
lean_object* v___y_32_ = stack[7].m_obj;
lean_object* v___y_33_ = stack[8].m_obj;
lean_object* v_res_36_;
v_res_36_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0(v_k_25_, v___y_26_, v___y_27_, v_b_28_, v_c_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0___boxed(lean_object* v_k_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v_b_40_, lean_object* v_c_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0(v_k_37_, v___y_38_, v___y_39_, v_b_40_, v_c_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_47_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(lean_object* v_type_48_, lean_object* v_k_49_, uint8_t v_cleanupAnnotations_50_, uint8_t v_whnfType_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___f_59_; lean_object* v___x_60_; 
lean_inc(v___y_53_);
lean_inc_ref(v___y_52_);
v___f_59_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_59_, 0, v_k_49_);
lean_closure_set(v___f_59_, 1, v___y_52_);
lean_closure_set(v___f_59_, 2, v___y_53_);
v___x_60_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_48_, v___f_59_, v_cleanupAnnotations_50_, v_whnfType_51_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
if (lean_obj_tag(v___x_60_) == 0)
{
return v___x_60_;
}
else
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_60_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_48_ = stack[0].m_obj;
lean_object* v_k_49_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_50_ = stack[2].m_num;
uint8_t v_whnfType_51_ = stack[3].m_num;
lean_object* v___y_52_ = stack[4].m_obj;
lean_object* v___y_53_ = stack[5].m_obj;
lean_object* v___y_54_ = stack[6].m_obj;
lean_object* v___y_55_ = stack[7].m_obj;
lean_object* v___y_56_ = stack[8].m_obj;
lean_object* v___y_57_ = stack[9].m_obj;
lean_object* v_res_69_;
v_res_69_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_type_48_, v_k_49_, v_cleanupAnnotations_50_, v_whnfType_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___boxed(lean_object* v_type_70_, lean_object* v_k_71_, lean_object* v_cleanupAnnotations_72_, lean_object* v_whnfType_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_81_; uint8_t v_whnfType_boxed_82_; lean_object* v_res_83_; 
v_cleanupAnnotations_boxed_81_ = lean_unbox(v_cleanupAnnotations_72_);
v_whnfType_boxed_82_ = lean_unbox(v_whnfType_73_);
v_res_83_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_type_70_, v_k_71_, v_cleanupAnnotations_boxed_81_, v_whnfType_boxed_82_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_83_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5(lean_object* v_00_u03b1_84_, lean_object* v_type_85_, lean_object* v_k_86_, uint8_t v_cleanupAnnotations_87_, uint8_t v_whnfType_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_type_85_, v_k_86_, v_cleanupAnnotations_87_, v_whnfType_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
return v___x_96_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_85_ = stack[1].m_obj;
lean_object* v_k_86_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_87_ = stack[3].m_num;
uint8_t v_whnfType_88_ = stack[4].m_num;
lean_object* v___y_89_ = stack[5].m_obj;
lean_object* v___y_90_ = stack[6].m_obj;
lean_object* v___y_91_ = stack[7].m_obj;
lean_object* v___y_92_ = stack[8].m_obj;
lean_object* v___y_93_ = stack[9].m_obj;
lean_object* v___y_94_ = stack[10].m_obj;
lean_object* v_res_97_;
v_res_97_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5(lean_box(0), v_type_85_, v_k_86_, v_cleanupAnnotations_87_, v_whnfType_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___boxed(lean_object* v_00_u03b1_98_, lean_object* v_type_99_, lean_object* v_k_100_, lean_object* v_cleanupAnnotations_101_, lean_object* v_whnfType_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_110_; uint8_t v_whnfType_boxed_111_; lean_object* v_res_112_; 
v_cleanupAnnotations_boxed_110_ = lean_unbox(v_cleanupAnnotations_101_);
v_whnfType_boxed_111_ = lean_unbox(v_whnfType_102_);
v_res_112_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5(v_00_u03b1_98_, v_type_99_, v_k_100_, v_cleanupAnnotations_boxed_110_, v_whnfType_boxed_111_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_112_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_instMonadEIO___redArg();
return v___x_113_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(lean_object* v_msg_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v_toApplicative_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_221_; 
v___x_128_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0);
v___x_129_ = l_StateRefT_x27_instMonad___redArg(v___x_128_);
v_toApplicative_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; 
v_unused_222_ = lean_ctor_get(v___x_129_, 1);
lean_dec(v_unused_222_);
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_221_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_toApplicative_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_221_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_toFunctor_134_; lean_object* v_toSeq_135_; lean_object* v_toSeqLeft_136_; lean_object* v_toSeqRight_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_219_; 
v_toFunctor_134_ = lean_ctor_get(v_toApplicative_130_, 0);
v_toSeq_135_ = lean_ctor_get(v_toApplicative_130_, 2);
v_toSeqLeft_136_ = lean_ctor_get(v_toApplicative_130_, 3);
v_toSeqRight_137_ = lean_ctor_get(v_toApplicative_130_, 4);
v_isSharedCheck_219_ = !lean_is_exclusive(v_toApplicative_130_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v_toApplicative_130_, 1);
lean_dec(v_unused_220_);
v___x_139_ = v_toApplicative_130_;
v_isShared_140_ = v_isSharedCheck_219_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_toSeqRight_137_);
lean_inc(v_toSeqLeft_136_);
lean_inc(v_toSeq_135_);
lean_inc(v_toFunctor_134_);
lean_dec(v_toApplicative_130_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_219_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___x_150_; 
v___f_141_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__1));
v___f_142_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_134_);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_143_, 0, v_toFunctor_134_);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_144_, 0, v_toFunctor_134_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v___f_143_);
lean_ctor_set(v___x_145_, 1, v___f_144_);
v___f_146_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_146_, 0, v_toSeqRight_137_);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_147_, 0, v_toSeqLeft_136_);
v___f_148_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_148_, 0, v_toSeq_135_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 4, v___f_146_);
lean_ctor_set(v___x_139_, 3, v___f_147_);
lean_ctor_set(v___x_139_, 2, v___f_148_);
lean_ctor_set(v___x_139_, 1, v___f_141_);
lean_ctor_set(v___x_139_, 0, v___x_145_);
v___x_150_ = v___x_139_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___f_141_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v___f_148_);
lean_ctor_set(v_reuseFailAlloc_218_, 3, v___f_147_);
lean_ctor_set(v_reuseFailAlloc_218_, 4, v___f_146_);
v___x_150_ = v_reuseFailAlloc_218_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_152_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___f_142_);
lean_ctor_set(v___x_132_, 0, v___x_150_);
v___x_152_ = v___x_132_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___f_142_);
v___x_152_ = v_reuseFailAlloc_217_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v_toApplicative_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_215_; 
v___x_153_ = l_StateRefT_x27_instMonad___redArg(v___x_152_);
v_toApplicative_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v___x_153_, 1);
lean_dec(v_unused_216_);
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_215_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_toApplicative_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_215_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v_toFunctor_158_; lean_object* v_toSeq_159_; lean_object* v_toSeqLeft_160_; lean_object* v_toSeqRight_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_213_; 
v_toFunctor_158_ = lean_ctor_get(v_toApplicative_154_, 0);
v_toSeq_159_ = lean_ctor_get(v_toApplicative_154_, 2);
v_toSeqLeft_160_ = lean_ctor_get(v_toApplicative_154_, 3);
v_toSeqRight_161_ = lean_ctor_get(v_toApplicative_154_, 4);
v_isSharedCheck_213_ = !lean_is_exclusive(v_toApplicative_154_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_toApplicative_154_, 1);
lean_dec(v_unused_214_);
v___x_163_ = v_toApplicative_154_;
v_isShared_164_ = v_isSharedCheck_213_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_toSeqRight_161_);
lean_inc(v_toSeqLeft_160_);
lean_inc(v_toSeq_159_);
lean_inc(v_toFunctor_158_);
lean_dec(v_toApplicative_154_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_213_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___x_174_; 
v___f_165_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__3));
v___f_166_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_158_);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_167_, 0, v_toFunctor_158_);
v___f_168_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_168_, 0, v_toFunctor_158_);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___f_167_);
lean_ctor_set(v___x_169_, 1, v___f_168_);
v___f_170_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_170_, 0, v_toSeqRight_161_);
v___f_171_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_171_, 0, v_toSeqLeft_160_);
v___f_172_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_172_, 0, v_toSeq_159_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 4, v___f_170_);
lean_ctor_set(v___x_163_, 3, v___f_171_);
lean_ctor_set(v___x_163_, 2, v___f_172_);
lean_ctor_set(v___x_163_, 1, v___f_165_);
lean_ctor_set(v___x_163_, 0, v___x_169_);
v___x_174_ = v___x_163_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___f_165_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v___f_172_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v___f_171_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v___f_170_);
v___x_174_ = v_reuseFailAlloc_212_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___f_166_);
lean_ctor_set(v___x_156_, 0, v___x_174_);
v___x_176_ = v___x_156_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___f_166_);
v___x_176_ = v_reuseFailAlloc_211_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; lean_object* v_toApplicative_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_209_; 
v___x_177_ = l_StateRefT_x27_instMonad___redArg(v___x_176_);
v_toApplicative_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v___x_177_, 1);
lean_dec(v_unused_210_);
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_209_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_toApplicative_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_209_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_toFunctor_182_; lean_object* v_toSeq_183_; lean_object* v_toSeqLeft_184_; lean_object* v_toSeqRight_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_207_; 
v_toFunctor_182_ = lean_ctor_get(v_toApplicative_178_, 0);
v_toSeq_183_ = lean_ctor_get(v_toApplicative_178_, 2);
v_toSeqLeft_184_ = lean_ctor_get(v_toApplicative_178_, 3);
v_toSeqRight_185_ = lean_ctor_get(v_toApplicative_178_, 4);
v_isSharedCheck_207_ = !lean_is_exclusive(v_toApplicative_178_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_toApplicative_178_, 1);
lean_dec(v_unused_208_);
v___x_187_ = v_toApplicative_178_;
v_isShared_188_ = v_isSharedCheck_207_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_toSeqRight_185_);
lean_inc(v_toSeqLeft_184_);
lean_inc(v_toSeq_183_);
lean_inc(v_toFunctor_182_);
lean_dec(v_toApplicative_178_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_207_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___x_198_; 
v___f_189_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__5));
v___f_190_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_182_);
v___f_191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_191_, 0, v_toFunctor_182_);
v___f_192_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_192_, 0, v_toFunctor_182_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___f_191_);
lean_ctor_set(v___x_193_, 1, v___f_192_);
v___f_194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_194_, 0, v_toSeqRight_185_);
v___f_195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_195_, 0, v_toSeqLeft_184_);
v___f_196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_196_, 0, v_toSeq_183_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 4, v___f_194_);
lean_ctor_set(v___x_187_, 3, v___f_195_);
lean_ctor_set(v___x_187_, 2, v___f_196_);
lean_ctor_set(v___x_187_, 1, v___f_189_);
lean_ctor_set(v___x_187_, 0, v___x_193_);
v___x_198_ = v___x_187_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___f_189_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v___f_196_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v___f_195_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v___f_194_);
v___x_198_ = v_reuseFailAlloc_206_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_200_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v___f_190_);
lean_ctor_set(v___x_180_, 0, v___x_198_);
v___x_200_ = v___x_180_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___f_190_);
v___x_200_ = v_reuseFailAlloc_205_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_30543__overap_203_; lean_object* v___x_204_; 
v___x_201_ = lean_box(0);
v___x_202_ = l_instInhabitedOfMonad___redArg(v___x_200_, v___x_201_);
v___x_30543__overap_203_ = lean_panic_fn_borrowed(v___x_202_, v_msg_120_);
lean_dec(v___x_202_);
lean_inc(v___y_126_);
lean_inc_ref(v___y_125_);
lean_inc(v___y_124_);
lean_inc_ref(v___y_123_);
lean_inc(v___y_122_);
lean_inc_ref(v___y_121_);
v___x_204_ = lean_apply_7(v___x_30543__overap_203_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, lean_box(0));
return v___x_204_;
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
}
}
}
}
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_120_ = stack[0].m_obj;
lean_object* v___y_121_ = stack[1].m_obj;
lean_object* v___y_122_ = stack[2].m_obj;
lean_object* v___y_123_ = stack[3].m_obj;
lean_object* v___y_124_ = stack[4].m_obj;
lean_object* v___y_125_ = stack[5].m_obj;
lean_object* v___y_126_ = stack[6].m_obj;
lean_object* v_res_223_;
v_res_223_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(v_msg_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
stack->m_obj
 = v_res_223_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(v_msg_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
return v_res_232_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; lean_object* v_env_240_; uint8_t v___x_241_; lean_object* v_env_242_; lean_object* v___x_243_; lean_object* v_toCold_244_; lean_object* v_mctx_245_; lean_object* v_lctx_246_; lean_object* v_options_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_239_ = lean_st_ref_get(v___y_237_);
v_env_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc_ref(v_env_240_);
lean_dec(v___x_239_);
v___x_241_ = 0;
v_env_242_ = l_Lean_Environment_setRecordingDeps(v_env_240_, v___x_241_);
v___x_243_ = lean_st_ref_get(v___y_235_);
v_toCold_244_ = lean_ctor_get(v___y_236_, 0);
v_mctx_245_ = lean_ctor_get(v___x_243_, 0);
lean_inc_ref(v_mctx_245_);
lean_dec(v___x_243_);
v_lctx_246_ = lean_ctor_get(v___y_234_, 2);
v_options_247_ = lean_ctor_get(v_toCold_244_, 2);
lean_inc_ref(v_options_247_);
lean_inc_ref(v_lctx_246_);
v___x_248_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_248_, 0, v_env_242_);
lean_ctor_set(v___x_248_, 1, v_mctx_245_);
lean_ctor_set(v___x_248_, 2, v_lctx_246_);
lean_ctor_set(v___x_248_, 3, v_options_247_);
v___x_249_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v_msgData_233_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_233_ = stack[0].m_obj;
lean_object* v___y_234_ = stack[1].m_obj;
lean_object* v___y_235_ = stack[2].m_obj;
lean_object* v___y_236_ = stack[3].m_obj;
lean_object* v___y_237_ = stack[4].m_obj;
lean_object* v_res_251_;
v_res_251_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msgData_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msgData_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
return v_res_258_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(1);
v___x_260_ = l_Lean_MessageData_ofFormat(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2));
v___x_265_ = l_Lean_MessageData_ofFormat(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12(lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
return v_x_266_;
}
else
{
lean_object* v_head_268_; lean_object* v_tail_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_291_; 
v_head_268_ = lean_ctor_get(v_x_267_, 0);
v_tail_269_ = lean_ctor_get(v_x_267_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_267_);
if (v_isSharedCheck_291_ == 0)
{
v___x_271_ = v_x_267_;
v_isShared_272_ = v_isSharedCheck_291_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_tail_269_);
lean_inc(v_head_268_);
lean_dec(v_x_267_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_291_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v_before_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_289_; 
v_before_273_ = lean_ctor_get(v_head_268_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v_head_268_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v_head_268_, 1);
lean_dec(v_unused_290_);
v___x_275_ = v_head_268_;
v_isShared_276_ = v_isSharedCheck_289_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_before_273_);
lean_dec(v_head_268_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_289_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_276_ == 0)
{
lean_ctor_set_tag(v___x_275_, 7);
lean_ctor_set(v___x_275_, 1, v___x_277_);
lean_ctor_set(v___x_275_, 0, v_x_266_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_x_266_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v___x_277_);
v___x_279_ = v_reuseFailAlloc_288_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3);
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 7);
lean_ctor_set(v___x_271_, 1, v___x_280_);
lean_ctor_set(v___x_271_, 0, v___x_279_);
v___x_282_ = v___x_271_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_280_);
v___x_282_ = v_reuseFailAlloc_287_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = l_Lean_MessageData_ofSyntax(v_before_273_);
v___x_284_ = l_Lean_indentD(v___x_283_);
v___x_285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_282_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v_x_266_ = v___x_285_;
v_x_267_ = v_tail_269_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_opts_292_, lean_object* v_opt_293_){
_start:
{
lean_object* v_name_294_; lean_object* v_defValue_295_; lean_object* v_map_296_; lean_object* v___x_297_; 
v_name_294_ = lean_ctor_get(v_opt_293_, 0);
v_defValue_295_ = lean_ctor_get(v_opt_293_, 1);
v_map_296_ = lean_ctor_get(v_opts_292_, 0);
v___x_297_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_296_, v_name_294_);
if (lean_obj_tag(v___x_297_) == 0)
{
uint8_t v___x_298_; 
v___x_298_ = lean_unbox(v_defValue_295_);
return v___x_298_;
}
else
{
lean_object* v_val_299_; 
v_val_299_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_val_299_);
lean_dec_ref_known(v___x_297_, 1);
if (lean_obj_tag(v_val_299_) == 1)
{
uint8_t v_v_300_; 
v_v_300_ = lean_ctor_get_uint8(v_val_299_, 0);
lean_dec_ref_known(v_val_299_, 0);
return v_v_300_;
}
else
{
uint8_t v___x_301_; 
lean_dec(v_val_299_);
v___x_301_ = lean_unbox(v_defValue_295_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_292_ = stack[0].m_obj;
lean_object* v_opt_293_ = stack[1].m_obj;
uint8_t v_res_302_;
v_res_302_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_292_, v_opt_293_);
stack->m_num = v_res_302_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_opts_303_, lean_object* v_opt_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_303_, v_opt_304_);
lean_dec_ref(v_opt_304_);
lean_dec_ref(v_opts_303_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_311_ = l_Lean_MessageData_ofFormat(v___x_310_);
return v___x_311_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_312_, lean_object* v_macroStack_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_316_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_314_);
v___x_317_ = l_Lean_Elab_pp_macroStack;
v___x_318_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(v___x_316_, v___x_317_);
lean_dec_ref(v___x_316_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; 
lean_dec(v_macroStack_313_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v_msgData_312_);
return v___x_319_;
}
else
{
if (lean_obj_tag(v_macroStack_313_) == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v_msgData_312_);
return v___x_320_;
}
else
{
lean_object* v_head_321_; lean_object* v_after_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_337_; 
v_head_321_ = lean_ctor_get(v_macroStack_313_, 0);
lean_inc(v_head_321_);
v_after_322_ = lean_ctor_get(v_head_321_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_head_321_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_head_321_, 0);
lean_dec(v_unused_338_);
v___x_324_ = v_head_321_;
v_isShared_325_ = v_isSharedCheck_337_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_after_322_);
lean_dec(v_head_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_337_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 7);
lean_ctor_set(v___x_324_, 1, v___x_326_);
lean_ctor_set(v___x_324_, 0, v_msgData_312_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_msgData_312_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_336_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_msgData_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_329_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_Lean_MessageData_ofSyntax(v_after_322_);
v___x_332_ = l_Lean_indentD(v___x_331_);
v_msgData_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_333_, 0, v___x_330_);
lean_ctor_set(v_msgData_333_, 1, v___x_332_);
v___x_334_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12(v_msgData_333_, v_macroStack_313_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_312_ = stack[0].m_obj;
lean_object* v_macroStack_313_ = stack[1].m_obj;
lean_object* v___y_314_ = stack[2].m_obj;
lean_object* v_res_339_;
v_res_339_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_312_, v_macroStack_313_, v___y_314_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_340_, lean_object* v_macroStack_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_340_, v_macroStack_341_, v___y_342_);
lean_dec_ref(v___y_342_);
return v_res_344_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_ref_353_; lean_object* v_macroStack_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_a_357_; lean_object* v___x_358_; lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_367_; 
v_ref_353_ = lean_ctor_get(v___y_350_, 2);
v_macroStack_354_ = lean_ctor_get(v___y_346_, 1);
v___x_355_ = l_Lean_Elab_getBetterRef(v_ref_353_, v_macroStack_354_);
v___x_356_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msg_345_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref(v___x_356_);
lean_inc(v_macroStack_354_);
v___x_358_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_357_, v_macroStack_354_, v___y_350_);
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_367_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_355_);
lean_ctor_set(v___x_363_, 1, v_a_359_);
if (v_isShared_362_ == 0)
{
lean_ctor_set_tag(v___x_361_, 1);
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_345_ = stack[0].m_obj;
lean_object* v___y_346_ = stack[1].m_obj;
lean_object* v___y_347_ = stack[2].m_obj;
lean_object* v___y_348_ = stack[3].m_obj;
lean_object* v___y_349_ = stack[4].m_obj;
lean_object* v___y_350_ = stack[5].m_obj;
lean_object* v___y_351_ = stack[6].m_obj;
lean_object* v_res_368_;
v_res_368_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v_msg_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
stack->m_obj
 = v_res_368_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v_msg_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_377_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__0));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__2));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_387_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__6));
v___x_388_ = lean_unsigned_to_nat(11u);
v___x_389_ = lean_unsigned_to_nat(122u);
v___x_390_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__5));
v___x_391_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__4));
v___x_392_ = l_mkPanicMessageWithDecl(v___x_391_, v___x_390_, v___x_389_, v___x_388_, v___x_387_);
return v___x_392_;
}
}
lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(lean_object* v_constName_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_409_; lean_object* v_env_410_; uint8_t v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_st_ref_get(v___y_399_);
v_env_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc_ref(v_env_410_);
lean_dec(v___x_409_);
v___x_411_ = 0;
lean_inc(v_constName_393_);
v___x_412_ = l_Lean_Environment_findAsync_x3f(v_env_410_, v_constName_393_, v___x_411_);
if (lean_obj_tag(v___x_412_) == 1)
{
lean_object* v_val_413_; uint8_t v_kind_414_; 
v_val_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_val_413_);
lean_dec_ref_known(v___x_412_, 1);
v_kind_414_ = lean_ctor_get_uint8(v_val_413_, sizeof(void*)*3);
if (v_kind_414_ == 6)
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_413_);
if (lean_obj_tag(v___x_415_) == 6)
{
lean_object* v_val_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_constName_393_);
v_val_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_val_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 0);
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_val_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v___x_415_);
v___x_424_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7);
v___x_425_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(v___x_424_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_434_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_434_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
if (lean_obj_tag(v_a_426_) == 0)
{
lean_del_object(v___x_428_);
goto v___jp_401_;
}
else
{
lean_object* v_val_430_; lean_object* v___x_432_; 
lean_dec(v_constName_393_);
v_val_430_ = lean_ctor_get(v_a_426_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v_a_426_, 1);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v_val_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_val_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec(v_constName_393_);
v_a_435_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_425_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_425_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
else
{
lean_dec(v_val_413_);
goto v___jp_401_;
}
}
else
{
lean_dec(v___x_412_);
goto v___jp_401_;
}
v___jp_401_:
{
lean_object* v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_402_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1);
v___x_403_ = 0;
v___x_404_ = l_Lean_MessageData_ofConstName(v_constName_393_, v___x_403_);
v___x_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_402_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v___x_407_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
return v___x_408_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_393_ = stack[0].m_obj;
lean_object* v___y_394_ = stack[1].m_obj;
lean_object* v___y_395_ = stack[2].m_obj;
lean_object* v___y_396_ = stack[3].m_obj;
lean_object* v___y_397_ = stack[4].m_obj;
lean_object* v___y_398_ = stack[5].m_obj;
lean_object* v___y_399_ = stack[6].m_obj;
lean_object* v_res_443_;
v_res_443_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(v_constName_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
stack->m_obj
 = v_res_443_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___boxed(lean_object* v_constName_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(v_constName_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_452_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(size_t v_sz_453_, size_t v_i_454_, lean_object* v_bs_455_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = lean_usize_dec_lt(v_i_454_, v_sz_453_);
if (v___x_456_ == 0)
{
return v_bs_455_;
}
else
{
lean_object* v_v_457_; lean_object* v___x_458_; lean_object* v_bs_x27_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; 
v_v_457_ = lean_array_uget(v_bs_455_, v_i_454_);
v___x_458_ = lean_unsigned_to_nat(0u);
v_bs_x27_459_ = lean_array_uset(v_bs_455_, v_i_454_, v___x_458_);
v___x_460_ = ((size_t)1ULL);
v___x_461_ = lean_usize_add(v_i_454_, v___x_460_);
v___x_462_ = lean_array_uset(v_bs_x27_459_, v_i_454_, v_v_457_);
v_i_454_ = v___x_461_;
v_bs_455_ = v___x_462_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_453_ = stack[0].m_num;
size_t v_i_454_ = stack[1].m_num;
lean_object* v_bs_455_ = stack[2].m_obj;
lean_object* v_res_464_;
v_res_464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_453_, v_i_454_, v_bs_455_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1___boxed(lean_object* v_sz_465_, lean_object* v_i_466_, lean_object* v_bs_467_){
_start:
{
size_t v_sz_boxed_468_; size_t v_i_boxed_469_; lean_object* v_res_470_; 
v_sz_boxed_468_ = lean_unbox_usize(v_sz_465_);
lean_dec(v_sz_465_);
v_i_boxed_469_ = lean_unbox_usize(v_i_466_);
lean_dec(v_i_466_);
v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_boxed_468_, v_i_boxed_469_, v_bs_467_);
return v_res_470_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(lean_object* v_upperBound_481_, lean_object* v_a_482_, lean_object* v_b_483_, lean_object* v___y_484_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = lean_nat_dec_lt(v_a_482_, v_upperBound_481_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec(v_a_482_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_b_483_);
return v___x_487_;
}
else
{
lean_object* v_ref_488_; uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_ref_488_ = lean_ctor_get(v___y_484_, 2);
v___x_489_ = 0;
v___x_490_ = l_Lean_SourceInfo_fromRef(v_ref_488_, v___x_489_);
v___x_491_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4));
v___x_492_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__5));
lean_inc(v___x_490_);
v___x_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_490_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = l_Lean_Syntax_node1(v___x_490_, v___x_491_, v___x_493_);
v___x_495_ = lean_array_push(v_b_483_, v___x_494_);
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = lean_nat_add(v_a_482_, v___x_496_);
lean_dec(v_a_482_);
v_a_482_ = v___x_497_;
v_b_483_ = v___x_495_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_481_ = stack[0].m_obj;
lean_object* v_a_482_ = stack[1].m_obj;
lean_object* v_b_483_ = stack[2].m_obj;
lean_object* v___y_484_ = stack[3].m_obj;
lean_object* v_res_499_;
v_res_499_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_upperBound_481_, v_a_482_, v_b_483_, v___y_484_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___boxed(lean_object* v_upperBound_500_, lean_object* v_a_501_, lean_object* v_b_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_upperBound_500_, v_a_501_, v_b_502_, v___y_503_);
lean_dec_ref(v___y_503_);
lean_dec(v_upperBound_500_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(lean_object* v_declName_506_, lean_object* v_as_507_, lean_object* v_j_508_){
_start:
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_array_get_size(v_as_507_);
v___x_510_ = lean_nat_dec_lt(v_j_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec(v_j_508_);
v___x_511_ = lean_box(0);
return v___x_511_;
}
else
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_array_fget_borrowed(v_as_507_, v_j_508_);
v___x_513_ = lean_name_eq(v___x_512_, v_declName_506_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_add(v_j_508_, v___x_514_);
lean_dec(v_j_508_);
v_j_508_ = v___x_515_;
goto _start;
}
else
{
lean_object* v___x_517_; 
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v_j_508_);
return v___x_517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___boxed(lean_object* v_declName_518_, lean_object* v_as_519_, lean_object* v_j_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(v_declName_518_, v_as_519_, v_j_520_);
lean_dec_ref(v_as_519_);
lean_dec(v_declName_518_);
return v_res_521_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_ref_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_ref_529_ = lean_ctor_get(v___y_526_, 2);
v___x_530_ = 0;
v___x_531_ = l_Lean_SourceInfo_fromRef(v_ref_529_, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_522_ = stack[0].m_obj;
lean_object* v___y_523_ = stack[1].m_obj;
lean_object* v___y_524_ = stack[2].m_obj;
lean_object* v___y_525_ = stack[3].m_obj;
lean_object* v___y_526_ = stack[4].m_obj;
lean_object* v___y_527_ = stack[5].m_obj;
lean_object* v_res_533_;
v_res_533_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0___boxed(lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_541_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__4));
v___x_553_ = l_String_toRawSubstring_x27(v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18));
v___x_583_ = l_String_toRawSubstring_x27(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36));
v___x_626_ = l_String_toRawSubstring_x27(v___x_625_);
return v___x_626_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(lean_object* v_upperBound_639_, lean_object* v___x_640_, lean_object* v_xs_641_, lean_object* v_allIndVals_642_, lean_object* v_ctx_643_, lean_object* v_a_644_, lean_object* v_b_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_a_654_; uint8_t v___x_658_; 
v___x_658_ = lean_nat_dec_lt(v_a_644_, v_upperBound_639_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
lean_dec(v_a_644_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v_b_645_);
return v___x_659_;
}
else
{
lean_object* v_fst_660_; lean_object* v_snd_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_843_; 
v_fst_660_ = lean_ctor_get(v_b_645_, 0);
v_snd_661_ = lean_ctor_get(v_b_645_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_b_645_);
if (v_isSharedCheck_843_ == 0)
{
v___x_663_ = v_b_645_;
v_isShared_664_ = v_isSharedCheck_843_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_snd_661_);
lean_inc(v_fst_660_);
lean_dec(v_b_645_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_843_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_665_ = l_Lean_instInhabitedExpr;
v___x_666_ = lean_box(0);
v___x_667_ = lean_nat_add(v___x_640_, v_a_644_);
v___x_668_ = lean_array_get_borrowed(v___x_665_, v_xs_641_, v___x_667_);
lean_dec(v___x_667_);
v___x_669_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1));
v___x_670_ = l_Lean_Core_mkFreshUserName(v___x_669_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = l_Lean_mkIdent(v_a_671_);
lean_inc(v___x_672_);
v___x_673_ = lean_array_push(v_fst_660_, v___x_672_);
lean_inc(v___y_651_);
lean_inc_ref(v___y_650_);
lean_inc(v___y_649_);
lean_inc_ref(v___y_648_);
lean_inc(v___x_668_);
v___x_674_ = lean_infer_type(v___x_668_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
lean_inc(v___y_651_);
lean_inc_ref(v___y_650_);
lean_inc(v___y_649_);
lean_inc_ref(v___y_648_);
v___x_676_ = lean_whnf(v_a_675_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = l_Lean_Expr_getAppFn(v_a_677_);
lean_dec(v_a_677_);
if (lean_obj_tag(v___x_678_) == 4)
{
lean_object* v_declName_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_declName_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_declName_679_);
lean_dec_ref_known(v___x_678_, 2);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(v_declName_679_, v_allIndVals_642_, v___x_680_);
lean_dec(v_declName_679_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_682_; 
v___x_682_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_toCold_683_; lean_object* v_a_684_; lean_object* v_quotContext_685_; lean_object* v_currMacroScope_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v_toCold_683_ = lean_ctor_get(v___y_650_, 0);
v_a_684_ = lean_ctor_get(v___x_682_, 0);
lean_inc_n(v_a_684_, 12);
lean_dec_ref_known(v___x_682_, 1);
v_quotContext_685_ = lean_ctor_get(v_toCold_683_, 8);
v_currMacroScope_686_ = lean_ctor_get(v_toCold_683_, 9);
v___x_687_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3));
v___x_688_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5);
v___x_689_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6));
lean_inc_n(v_currMacroScope_686_, 3);
lean_inc_n(v_quotContext_685_, 3);
v___x_690_ = l_Lean_addMacroScope(v_quotContext_685_, v___x_689_, v_currMacroScope_686_);
v___x_691_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8));
v___x_692_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_692_, 0, v_a_684_);
lean_ctor_set(v___x_692_, 1, v___x_688_);
lean_ctor_set(v___x_692_, 2, v___x_690_);
lean_ctor_set(v___x_692_, 3, v___x_691_);
v___x_693_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_694_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12));
v___x_695_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14));
v___x_696_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15));
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v_a_684_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17));
v___x_699_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19);
v___x_700_ = l_Lean_addMacroScope(v_quotContext_685_, v___x_666_, v_currMacroScope_686_);
v___x_701_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35));
v___x_702_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_702_, 0, v_a_684_);
lean_ctor_set(v___x_702_, 1, v___x_699_);
lean_ctor_set(v___x_702_, 2, v___x_700_);
lean_ctor_set(v___x_702_, 3, v___x_701_);
v___x_703_ = l_Lean_Syntax_node1(v_a_684_, v___x_698_, v___x_702_);
v___x_704_ = l_Lean_Syntax_node2(v_a_684_, v___x_695_, v___x_697_, v___x_703_);
v___x_705_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37);
v___x_706_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38));
v___x_707_ = l_Lean_addMacroScope(v_quotContext_685_, v___x_706_, v_currMacroScope_686_);
v___x_708_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41));
v___x_709_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_709_, 0, v_a_684_);
lean_ctor_set(v___x_709_, 1, v___x_705_);
lean_ctor_set(v___x_709_, 2, v___x_707_);
lean_ctor_set(v___x_709_, 3, v___x_708_);
v___x_710_ = l_Lean_Syntax_node1(v_a_684_, v___x_693_, v___x_672_);
v___x_711_ = l_Lean_Syntax_node2(v_a_684_, v___x_687_, v___x_709_, v___x_710_);
v___x_712_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42));
v___x_713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_713_, 0, v_a_684_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_Syntax_node3(v_a_684_, v___x_694_, v___x_704_, v___x_711_, v___x_713_);
v___x_715_ = l_Lean_Syntax_node2(v_a_684_, v___x_693_, v_snd_661_, v___x_714_);
v___x_716_ = l_Lean_Syntax_node2(v_a_684_, v___x_687_, v___x_692_, v___x_715_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_716_);
lean_ctor_set(v___x_663_, 0, v___x_673_);
v___x_718_ = v___x_663_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
v_a_654_ = v___x_718_;
goto v___jp_653_;
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v___x_673_);
lean_dec(v___x_672_);
lean_del_object(v___x_663_);
lean_dec(v_snd_661_);
lean_dec(v_a_644_);
v_a_720_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_682_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_682_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
else
{
lean_object* v_val_728_; lean_object* v___x_729_; 
v_val_728_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v___x_681_, 1);
v___x_729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_toCold_730_; lean_object* v_a_731_; lean_object* v_quotContext_732_; lean_object* v_currMacroScope_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v_auxFunNames_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v_toCold_730_ = lean_ctor_get(v___y_650_, 0);
v_a_731_ = lean_ctor_get(v___x_729_, 0);
lean_inc_n(v_a_731_, 11);
lean_dec_ref_known(v___x_729_, 1);
v_quotContext_732_ = lean_ctor_get(v_toCold_730_, 8);
v_currMacroScope_733_ = lean_ctor_get(v_toCold_730_, 9);
v___x_734_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3));
v___x_735_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5);
v___x_736_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6));
lean_inc_n(v_currMacroScope_733_, 2);
lean_inc_n(v_quotContext_732_, 2);
v___x_737_ = l_Lean_addMacroScope(v_quotContext_732_, v___x_736_, v_currMacroScope_733_);
v___x_738_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8));
v___x_739_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_739_, 0, v_a_731_);
lean_ctor_set(v___x_739_, 1, v___x_735_);
lean_ctor_set(v___x_739_, 2, v___x_737_);
lean_ctor_set(v___x_739_, 3, v___x_738_);
v___x_740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12));
v___x_741_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14));
v___x_742_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15));
v___x_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_743_, 0, v_a_731_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19);
v___x_745_ = l_Lean_addMacroScope(v_quotContext_732_, v___x_666_, v_currMacroScope_733_);
v___x_746_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35));
v___x_747_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_747_, 0, v_a_731_);
lean_ctor_set(v___x_747_, 1, v___x_744_);
lean_ctor_set(v___x_747_, 2, v___x_745_);
lean_ctor_set(v___x_747_, 3, v___x_746_);
v_auxFunNames_748_ = lean_ctor_get(v_ctx_643_, 2);
v___x_749_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17));
v___x_750_ = l_Lean_Syntax_node1(v_a_731_, v___x_749_, v___x_747_);
v___x_751_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_752_ = l_Lean_Syntax_node2(v_a_731_, v___x_741_, v___x_743_, v___x_750_);
v___x_753_ = lean_array_get_borrowed(v___x_666_, v_auxFunNames_748_, v_val_728_);
lean_dec(v_val_728_);
lean_inc(v___x_753_);
v___x_754_ = l_Lean_mkIdent(v___x_753_);
v___x_755_ = l_Lean_Syntax_node1(v_a_731_, v___x_751_, v___x_672_);
v___x_756_ = l_Lean_Syntax_node2(v_a_731_, v___x_734_, v___x_754_, v___x_755_);
v___x_757_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42));
v___x_758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_758_, 0, v_a_731_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = l_Lean_Syntax_node3(v_a_731_, v___x_740_, v___x_752_, v___x_756_, v___x_758_);
v___x_760_ = l_Lean_Syntax_node2(v_a_731_, v___x_751_, v_snd_661_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node2(v_a_731_, v___x_734_, v___x_739_, v___x_760_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_761_);
lean_ctor_set(v___x_663_, 0, v___x_673_);
v___x_763_ = v___x_663_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
v_a_654_ = v___x_763_;
goto v___jp_653_;
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_val_728_);
lean_dec_ref(v___x_673_);
lean_dec(v___x_672_);
lean_del_object(v___x_663_);
lean_dec(v_snd_661_);
lean_dec(v_a_644_);
v_a_765_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_729_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_729_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
else
{
lean_object* v___x_773_; 
lean_dec_ref(v___x_678_);
v___x_773_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_toCold_774_; lean_object* v_a_775_; lean_object* v_quotContext_776_; lean_object* v_currMacroScope_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v_toCold_774_ = lean_ctor_get(v___y_650_, 0);
v_a_775_ = lean_ctor_get(v___x_773_, 0);
lean_inc_n(v_a_775_, 12);
lean_dec_ref_known(v___x_773_, 1);
v_quotContext_776_ = lean_ctor_get(v_toCold_774_, 8);
v_currMacroScope_777_ = lean_ctor_get(v_toCold_774_, 9);
v___x_778_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3));
v___x_779_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5);
v___x_780_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6));
lean_inc_n(v_currMacroScope_777_, 3);
lean_inc_n(v_quotContext_776_, 3);
v___x_781_ = l_Lean_addMacroScope(v_quotContext_776_, v___x_780_, v_currMacroScope_777_);
v___x_782_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8));
v___x_783_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_783_, 0, v_a_775_);
lean_ctor_set(v___x_783_, 1, v___x_779_);
lean_ctor_set(v___x_783_, 2, v___x_781_);
lean_ctor_set(v___x_783_, 3, v___x_782_);
v___x_784_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_785_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12));
v___x_786_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14));
v___x_787_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15));
v___x_788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_775_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17));
v___x_790_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19);
v___x_791_ = l_Lean_addMacroScope(v_quotContext_776_, v___x_666_, v_currMacroScope_777_);
v___x_792_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35));
v___x_793_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_793_, 0, v_a_775_);
lean_ctor_set(v___x_793_, 1, v___x_790_);
lean_ctor_set(v___x_793_, 2, v___x_791_);
lean_ctor_set(v___x_793_, 3, v___x_792_);
v___x_794_ = l_Lean_Syntax_node1(v_a_775_, v___x_789_, v___x_793_);
v___x_795_ = l_Lean_Syntax_node2(v_a_775_, v___x_786_, v___x_788_, v___x_794_);
v___x_796_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37);
v___x_797_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38));
v___x_798_ = l_Lean_addMacroScope(v_quotContext_776_, v___x_797_, v_currMacroScope_777_);
v___x_799_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41));
v___x_800_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_800_, 0, v_a_775_);
lean_ctor_set(v___x_800_, 1, v___x_796_);
lean_ctor_set(v___x_800_, 2, v___x_798_);
lean_ctor_set(v___x_800_, 3, v___x_799_);
v___x_801_ = l_Lean_Syntax_node1(v_a_775_, v___x_784_, v___x_672_);
v___x_802_ = l_Lean_Syntax_node2(v_a_775_, v___x_778_, v___x_800_, v___x_801_);
v___x_803_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42));
v___x_804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_804_, 0, v_a_775_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = l_Lean_Syntax_node3(v_a_775_, v___x_785_, v___x_795_, v___x_802_, v___x_804_);
v___x_806_ = l_Lean_Syntax_node2(v_a_775_, v___x_784_, v_snd_661_, v___x_805_);
v___x_807_ = l_Lean_Syntax_node2(v_a_775_, v___x_778_, v___x_783_, v___x_806_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_807_);
lean_ctor_set(v___x_663_, 0, v___x_673_);
v___x_809_ = v___x_663_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v_a_654_ = v___x_809_;
goto v___jp_653_;
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v___x_673_);
lean_dec(v___x_672_);
lean_del_object(v___x_663_);
lean_dec(v_snd_661_);
lean_dec(v_a_644_);
v_a_811_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_773_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_773_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v___x_673_);
lean_dec(v___x_672_);
lean_del_object(v___x_663_);
lean_dec(v_snd_661_);
lean_dec(v_a_644_);
v_a_819_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_676_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_676_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec_ref(v___x_673_);
lean_dec(v___x_672_);
lean_del_object(v___x_663_);
lean_dec(v_snd_661_);
lean_dec(v_a_644_);
v_a_827_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_674_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_674_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_del_object(v___x_663_);
lean_dec(v_snd_661_);
lean_dec(v_fst_660_);
lean_dec(v_a_644_);
v_a_835_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_670_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_670_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
v___jp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_unsigned_to_nat(1u);
v___x_656_ = lean_nat_add(v_a_644_, v___x_655_);
lean_dec(v_a_644_);
v_a_644_ = v___x_656_;
v_b_645_ = v_a_654_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_639_ = stack[0].m_obj;
lean_object* v___x_640_ = stack[1].m_obj;
lean_object* v_xs_641_ = stack[2].m_obj;
lean_object* v_allIndVals_642_ = stack[3].m_obj;
lean_object* v_ctx_643_ = stack[4].m_obj;
lean_object* v_a_644_ = stack[5].m_obj;
lean_object* v_b_645_ = stack[6].m_obj;
lean_object* v___y_646_ = stack[7].m_obj;
lean_object* v___y_647_ = stack[8].m_obj;
lean_object* v___y_648_ = stack[9].m_obj;
lean_object* v___y_649_ = stack[10].m_obj;
lean_object* v___y_650_ = stack[11].m_obj;
lean_object* v___y_651_ = stack[12].m_obj;
lean_object* v_res_844_;
v_res_844_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_upperBound_639_, v___x_640_, v_xs_641_, v_allIndVals_642_, v_ctx_643_, v_a_644_, v_b_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_845_, lean_object* v___x_846_, lean_object* v_xs_847_, lean_object* v_allIndVals_848_, lean_object* v_ctx_849_, lean_object* v_a_850_, lean_object* v_b_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_upperBound_845_, v___x_846_, v_xs_847_, v_allIndVals_848_, v_ctx_849_, v_a_850_, v_b_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec_ref(v_ctx_849_);
lean_dec_ref(v_allIndVals_848_);
lean_dec_ref(v_xs_847_);
lean_dec(v___x_846_);
lean_dec(v_upperBound_845_);
return v_res_859_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Array_mkArray0___redArg();
return v___x_867_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__7));
v___x_877_ = l_Lean_mkAtom(v___x_876_);
return v___x_877_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1(lean_object* v_indVal_879_, lean_object* v___x_880_, lean_object* v_alts_881_, lean_object* v_snd_882_, lean_object* v_numFields_883_, lean_object* v_allIndVals_884_, lean_object* v_ctx_885_, lean_object* v___f_886_, lean_object* v_head_887_, lean_object* v_xs_888_, lean_object* v_x_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_numParams_897_; lean_object* v_numIndices_898_; lean_object* v___x_899_; 
v_numParams_897_ = lean_ctor_get(v_indVal_879_, 1);
v_numIndices_898_ = lean_ctor_get(v_indVal_879_, 2);
lean_inc_ref(v_alts_881_);
lean_inc(v___x_880_);
v___x_899_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_numIndices_898_, v___x_880_, v_alts_881_, v___y_894_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_901_ = l_Nat_reprFast(v_snd_882_);
v___x_902_ = lean_box(2);
v___x_903_ = l_Lean_Syntax_mkNumLit(v___x_901_, v___x_902_);
lean_inc(v___x_880_);
v___x_904_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_numParams_897_, v___x_880_, v_alts_881_, v___y_894_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v_a_905_);
lean_ctor_set(v___x_906_, 1, v___x_903_);
v___x_907_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_numFields_883_, v_numParams_897_, v_xs_888_, v_allIndVals_884_, v_ctx_885_, v___x_880_, v___x_906_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v_fst_909_; lean_object* v_snd_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_969_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_907_, 1);
v_fst_909_ = lean_ctor_get(v_a_908_, 0);
v_snd_910_ = lean_ctor_get(v_a_908_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_a_908_);
if (v_isSharedCheck_969_ == 0)
{
v___x_912_ = v_a_908_;
v_isShared_913_ = v_isSharedCheck_969_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_snd_910_);
lean_inc(v_fst_909_);
lean_dec(v_a_908_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_969_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; 
lean_inc_ref(v___f_886_);
lean_inc(v___y_895_);
lean_inc_ref(v___y_894_);
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
v___x_914_ = lean_apply_7(v___f_886_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, lean_box(0));
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc_n(v_a_915_, 2);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3));
v___x_917_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1));
v___x_918_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2));
if (v_isShared_913_ == 0)
{
lean_ctor_set_tag(v___x_912_, 2);
lean_ctor_set(v___x_912_, 1, v___x_918_);
lean_ctor_set(v___x_912_, 0, v_a_915_);
v___x_920_ = v___x_912_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_915_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v___x_918_);
v___x_920_ = v_reuseFailAlloc_960_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_921_ = l_Lean_mkIdent(v_head_887_);
lean_inc_n(v_a_915_, 2);
v___x_922_ = l_Lean_Syntax_node2(v_a_915_, v___x_917_, v___x_920_, v___x_921_);
v___x_923_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_924_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_925_ = l_Array_append___redArg(v___x_924_, v_fst_909_);
lean_dec(v_fst_909_);
v___x_926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_926_, 0, v_a_915_);
lean_ctor_set(v___x_926_, 1, v___x_923_);
lean_ctor_set(v___x_926_, 2, v___x_925_);
v___x_927_ = l_Lean_Syntax_node2(v_a_915_, v___x_916_, v___x_922_, v___x_926_);
v___x_928_ = lean_array_push(v_a_900_, v___x_927_);
lean_inc(v___y_895_);
lean_inc_ref(v___y_894_);
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
v___x_929_ = lean_apply_7(v___f_886_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, lean_box(0));
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_951_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_951_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_951_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_951_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; size_t v_sz_937_; size_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_934_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5));
v___x_935_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__6));
lean_inc_n(v_a_930_, 4);
v___x_936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_936_, 0, v_a_930_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v_sz_937_ = lean_array_size(v___x_928_);
v___x_938_ = ((size_t)0ULL);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_937_, v___x_938_, v___x_928_);
v___x_940_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8);
v___x_941_ = l_Lean_mkSepArray(v___x_939_, v___x_940_);
lean_dec_ref(v___x_939_);
v___x_942_ = l_Array_append___redArg(v___x_924_, v___x_941_);
lean_dec_ref(v___x_941_);
v___x_943_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_943_, 0, v_a_930_);
lean_ctor_set(v___x_943_, 1, v___x_923_);
lean_ctor_set(v___x_943_, 2, v___x_942_);
v___x_944_ = l_Lean_Syntax_node1(v_a_930_, v___x_923_, v___x_943_);
v___x_945_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__9));
v___x_946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_946_, 0, v_a_930_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Lean_Syntax_node4(v_a_930_, v___x_934_, v___x_936_, v___x_944_, v___x_946_, v_snd_910_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_947_);
v___x_949_ = v___x_932_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec_ref(v___x_928_);
lean_dec(v_snd_910_);
v_a_952_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_929_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_929_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_del_object(v___x_912_);
lean_dec(v_snd_910_);
lean_dec(v_fst_909_);
lean_dec(v_a_900_);
lean_dec(v_head_887_);
lean_dec_ref(v___f_886_);
v_a_961_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_914_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_914_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec(v_a_900_);
lean_dec(v_head_887_);
lean_dec_ref(v___f_886_);
v_a_970_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_907_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_907_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
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
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v___x_903_);
lean_dec(v_a_900_);
lean_dec(v_head_887_);
lean_dec_ref(v___f_886_);
lean_dec(v___x_880_);
v_a_978_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_904_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_904_);
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
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_head_887_);
lean_dec_ref(v___f_886_);
lean_dec(v_snd_882_);
lean_dec_ref(v_alts_881_);
lean_dec(v___x_880_);
v_a_986_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_899_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_899_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
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
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_879_ = stack[0].m_obj;
lean_object* v___x_880_ = stack[1].m_obj;
lean_object* v_alts_881_ = stack[2].m_obj;
lean_object* v_snd_882_ = stack[3].m_obj;
lean_object* v_numFields_883_ = stack[4].m_obj;
lean_object* v_allIndVals_884_ = stack[5].m_obj;
lean_object* v_ctx_885_ = stack[6].m_obj;
lean_object* v___f_886_ = stack[7].m_obj;
lean_object* v_head_887_ = stack[8].m_obj;
lean_object* v_xs_888_ = stack[9].m_obj;
lean_object* v_x_889_ = stack[10].m_obj;
lean_object* v___y_890_ = stack[11].m_obj;
lean_object* v___y_891_ = stack[12].m_obj;
lean_object* v___y_892_ = stack[13].m_obj;
lean_object* v___y_893_ = stack[14].m_obj;
lean_object* v___y_894_ = stack[15].m_obj;
lean_object* v___y_895_ = stack[16].m_obj;
lean_object* v_res_994_;
v_res_994_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1(v_indVal_879_, v___x_880_, v_alts_881_, v_snd_882_, v_numFields_883_, v_allIndVals_884_, v_ctx_885_, v___f_886_, v_head_887_, v_xs_888_, v_x_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
stack->m_obj
 = v_res_994_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_995_ = _args[0];
lean_object* v___x_996_ = _args[1];
lean_object* v_alts_997_ = _args[2];
lean_object* v_snd_998_ = _args[3];
lean_object* v_numFields_999_ = _args[4];
lean_object* v_allIndVals_1000_ = _args[5];
lean_object* v_ctx_1001_ = _args[6];
lean_object* v___f_1002_ = _args[7];
lean_object* v_head_1003_ = _args[8];
lean_object* v_xs_1004_ = _args[9];
lean_object* v_x_1005_ = _args[10];
lean_object* v___y_1006_ = _args[11];
lean_object* v___y_1007_ = _args[12];
lean_object* v___y_1008_ = _args[13];
lean_object* v___y_1009_ = _args[14];
lean_object* v___y_1010_ = _args[15];
lean_object* v___y_1011_ = _args[16];
lean_object* v___y_1012_ = _args[17];
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1(v_indVal_995_, v___x_996_, v_alts_997_, v_snd_998_, v_numFields_999_, v_allIndVals_1000_, v_ctx_1001_, v___f_1002_, v_head_1003_, v_xs_1004_, v_x_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec_ref(v_x_1005_);
lean_dec_ref(v_xs_1004_);
lean_dec_ref(v_ctx_1001_);
lean_dec_ref(v_allIndVals_1000_);
lean_dec(v_numFields_999_);
lean_dec_ref(v_indVal_995_);
return v_res_1013_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0(lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_ref_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_ref_1021_ = lean_ctor_get(v___y_1018_, 2);
v___x_1022_ = 0;
v___x_1023_ = l_Lean_SourceInfo_fromRef(v_ref_1021_, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1014_ = stack[0].m_obj;
lean_object* v___y_1015_ = stack[1].m_obj;
lean_object* v___y_1016_ = stack[2].m_obj;
lean_object* v___y_1017_ = stack[3].m_obj;
lean_object* v___y_1018_ = stack[4].m_obj;
lean_object* v___y_1019_ = stack[5].m_obj;
lean_object* v_res_1025_;
v_res_1025_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0(v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
stack->m_obj
 = v_res_1025_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0___boxed(lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0(v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1033_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(lean_object* v_indVal_1037_, lean_object* v_allIndVals_1038_, lean_object* v_ctx_1039_, lean_object* v_as_x27_1040_, lean_object* v_b_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
if (lean_obj_tag(v_as_x27_1040_) == 0)
{
lean_object* v___x_1049_; 
lean_dec_ref(v_ctx_1039_);
lean_dec_ref(v_allIndVals_1038_);
lean_dec_ref(v_indVal_1037_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_b_1041_);
return v___x_1049_;
}
else
{
lean_object* v_head_1050_; lean_object* v_tail_1051_; lean_object* v_fst_1052_; lean_object* v_snd_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1092_; 
v_head_1050_ = lean_ctor_get(v_as_x27_1040_, 0);
v_tail_1051_ = lean_ctor_get(v_as_x27_1040_, 1);
v_fst_1052_ = lean_ctor_get(v_b_1041_, 0);
v_snd_1053_ = lean_ctor_get(v_b_1041_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_b_1041_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1055_ = v_b_1041_;
v_isShared_1056_ = v_isSharedCheck_1092_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_snd_1053_);
lean_inc(v_fst_1052_);
lean_dec(v_b_1041_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1092_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v_alts_1059_; lean_object* v___x_1060_; 
v___f_1057_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__0));
v___x_1058_ = lean_unsigned_to_nat(0u);
v_alts_1059_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1));
lean_inc(v_head_1050_);
v___x_1060_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(v_head_1050_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v_toConstantVal_1062_; lean_object* v_numFields_1063_; lean_object* v_type_1064_; lean_object* v___f_1065_; uint8_t v___x_1066_; lean_object* v___x_1067_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
v_toConstantVal_1062_ = lean_ctor_get(v_a_1061_, 0);
lean_inc_ref(v_toConstantVal_1062_);
v_numFields_1063_ = lean_ctor_get(v_a_1061_, 4);
lean_inc(v_numFields_1063_);
lean_dec(v_a_1061_);
v_type_1064_ = lean_ctor_get(v_toConstantVal_1062_, 2);
lean_inc_ref(v_type_1064_);
lean_dec_ref(v_toConstantVal_1062_);
lean_inc(v_head_1050_);
lean_inc_ref(v_ctx_1039_);
lean_inc_ref(v_allIndVals_1038_);
lean_inc(v_snd_1053_);
lean_inc_ref(v_indVal_1037_);
v___f_1065_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___boxed), 18, 9);
lean_closure_set(v___f_1065_, 0, v_indVal_1037_);
lean_closure_set(v___f_1065_, 1, v___x_1058_);
lean_closure_set(v___f_1065_, 2, v_alts_1059_);
lean_closure_set(v___f_1065_, 3, v_snd_1053_);
lean_closure_set(v___f_1065_, 4, v_numFields_1063_);
lean_closure_set(v___f_1065_, 5, v_allIndVals_1038_);
lean_closure_set(v___f_1065_, 6, v_ctx_1039_);
lean_closure_set(v___f_1065_, 7, v___f_1057_);
lean_closure_set(v___f_1065_, 8, v_head_1050_);
v___x_1066_ = 0;
v___x_1067_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_type_1064_, v___f_1065_, v___x_1066_, v___x_1066_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = lean_array_push(v_fst_1052_, v_a_1068_);
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = lean_nat_add(v_snd_1053_, v___x_1070_);
lean_dec(v_snd_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v___x_1071_);
lean_ctor_set(v___x_1055_, 0, v___x_1069_);
v___x_1073_ = v___x_1055_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
v_as_x27_1040_ = v_tail_1051_;
v_b_1041_ = v___x_1073_;
goto _start;
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_del_object(v___x_1055_);
lean_dec(v_snd_1053_);
lean_dec(v_fst_1052_);
lean_dec_ref(v_ctx_1039_);
lean_dec_ref(v_allIndVals_1038_);
lean_dec_ref(v_indVal_1037_);
v_a_1076_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1067_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1067_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_del_object(v___x_1055_);
lean_dec(v_snd_1053_);
lean_dec(v_fst_1052_);
lean_dec_ref(v_ctx_1039_);
lean_dec_ref(v_allIndVals_1038_);
lean_dec_ref(v_indVal_1037_);
v_a_1084_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1060_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1060_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_1037_ = stack[0].m_obj;
lean_object* v_allIndVals_1038_ = stack[1].m_obj;
lean_object* v_ctx_1039_ = stack[2].m_obj;
lean_object* v_as_x27_1040_ = stack[3].m_obj;
lean_object* v_b_1041_ = stack[4].m_obj;
lean_object* v___y_1042_ = stack[5].m_obj;
lean_object* v___y_1043_ = stack[6].m_obj;
lean_object* v___y_1044_ = stack[7].m_obj;
lean_object* v___y_1045_ = stack[8].m_obj;
lean_object* v___y_1046_ = stack[9].m_obj;
lean_object* v___y_1047_ = stack[10].m_obj;
lean_object* v_res_1093_;
v_res_1093_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(v_indVal_1037_, v_allIndVals_1038_, v_ctx_1039_, v_as_x27_1040_, v_b_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
stack->m_obj
 = v_res_1093_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___boxed(lean_object* v_indVal_1094_, lean_object* v_allIndVals_1095_, lean_object* v_ctx_1096_, lean_object* v_as_x27_1097_, lean_object* v_b_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(v_indVal_1094_, v_allIndVals_1095_, v_ctx_1096_, v_as_x27_1097_, v_b_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v_as_x27_1097_);
return v_res_1106_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7(size_t v_sz_1107_, size_t v_i_1108_, lean_object* v_bs_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_usize_dec_lt(v_i_1108_, v_sz_1107_);
if (v___x_1110_ == 0)
{
return v_bs_1109_;
}
else
{
lean_object* v_v_1111_; lean_object* v___x_1112_; lean_object* v_bs_x27_1113_; size_t v___x_1114_; size_t v___x_1115_; lean_object* v___x_1116_; 
v_v_1111_ = lean_array_uget(v_bs_1109_, v_i_1108_);
v___x_1112_ = lean_unsigned_to_nat(0u);
v_bs_x27_1113_ = lean_array_uset(v_bs_1109_, v_i_1108_, v___x_1112_);
v___x_1114_ = ((size_t)1ULL);
v___x_1115_ = lean_usize_add(v_i_1108_, v___x_1114_);
v___x_1116_ = lean_array_uset(v_bs_x27_1113_, v_i_1108_, v_v_1111_);
v_i_1108_ = v___x_1115_;
v_bs_1109_ = v___x_1116_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1107_ = stack[0].m_num;
size_t v_i_1108_ = stack[1].m_num;
lean_object* v_bs_1109_ = stack[2].m_obj;
lean_object* v_res_1118_;
v_res_1118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7(v_sz_1107_, v_i_1108_, v_bs_1109_);
stack->m_obj
 = v_res_1118_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7___boxed(lean_object* v_sz_1119_, lean_object* v_i_1120_, lean_object* v_bs_1121_){
_start:
{
size_t v_sz_boxed_1122_; size_t v_i_boxed_1123_; lean_object* v_res_1124_; 
v_sz_boxed_1122_ = lean_unbox_usize(v_sz_1119_);
lean_dec(v_sz_1119_);
v_i_boxed_1123_ = lean_unbox_usize(v_i_1120_);
lean_dec(v_i_1120_);
v_res_1124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7(v_sz_boxed_1122_, v_i_boxed_1123_, v_bs_1121_);
return v_res_1124_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(lean_object* v_ctx_1128_, lean_object* v_indVal_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_all_1137_; lean_object* v_ctors_1138_; lean_object* v_allIndVals_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_all_1137_ = lean_ctor_get(v_indVal_1129_, 3);
v_ctors_1138_ = lean_ctor_get(v_indVal_1129_, 4);
lean_inc(v_ctors_1138_);
lean_inc(v_all_1137_);
v_allIndVals_1139_ = lean_array_mk(v_all_1137_);
v___x_1140_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0));
v___x_1141_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(v_indVal_1129_, v_allIndVals_1139_, v_ctx_1128_, v_ctors_1138_, v___x_1140_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_ctors_1138_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1153_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1153_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1153_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_fst_1146_; size_t v_sz_1147_; size_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v_fst_1146_ = lean_ctor_get(v_a_1142_, 0);
lean_inc(v_fst_1146_);
lean_dec(v_a_1142_);
v_sz_1147_ = lean_array_size(v_fst_1146_);
v___x_1148_ = ((size_t)0ULL);
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7(v_sz_1147_, v___x_1148_, v_fst_1146_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1149_);
v___x_1151_ = v___x_1144_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
v_a_1154_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1141_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1141_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1128_ = stack[0].m_obj;
lean_object* v_indVal_1129_ = stack[1].m_obj;
lean_object* v_a_1130_ = stack[2].m_obj;
lean_object* v_a_1131_ = stack[3].m_obj;
lean_object* v_a_1132_ = stack[4].m_obj;
lean_object* v_a_1133_ = stack[5].m_obj;
lean_object* v_a_1134_ = stack[6].m_obj;
lean_object* v_a_1135_ = stack[7].m_obj;
lean_object* v_res_1162_;
v_res_1162_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(v_ctx_1128_, v_indVal_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
stack->m_obj
 = v_res_1162_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___boxed(lean_object* v_ctx_1163_, lean_object* v_indVal_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(v_ctx_1163_, v_indVal_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
return v_res_1172_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3(lean_object* v_upperBound_1173_, lean_object* v___x_1174_, lean_object* v_xs_1175_, lean_object* v_allIndVals_1176_, lean_object* v_ctx_1177_, lean_object* v_inst_1178_, lean_object* v_R_1179_, lean_object* v_a_1180_, lean_object* v_b_1181_, lean_object* v_c_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_upperBound_1173_, v___x_1174_, v_xs_1175_, v_allIndVals_1176_, v_ctx_1177_, v_a_1180_, v_b_1181_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1173_ = stack[0].m_obj;
lean_object* v___x_1174_ = stack[1].m_obj;
lean_object* v_xs_1175_ = stack[2].m_obj;
lean_object* v_allIndVals_1176_ = stack[3].m_obj;
lean_object* v_ctx_1177_ = stack[4].m_obj;
lean_object* v_a_1180_ = stack[7].m_obj;
lean_object* v_b_1181_ = stack[8].m_obj;
lean_object* v___y_1183_ = stack[10].m_obj;
lean_object* v___y_1184_ = stack[11].m_obj;
lean_object* v___y_1185_ = stack[12].m_obj;
lean_object* v___y_1186_ = stack[13].m_obj;
lean_object* v___y_1187_ = stack[14].m_obj;
lean_object* v___y_1188_ = stack[15].m_obj;
lean_object* v_res_1191_;
v_res_1191_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3(v_upperBound_1173_, v___x_1174_, v_xs_1175_, v_allIndVals_1176_, v_ctx_1177_, lean_box(0), lean_box(0), v_a_1180_, v_b_1181_, lean_box(0), v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
stack->m_obj
 = v_res_1191_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1192_ = _args[0];
lean_object* v___x_1193_ = _args[1];
lean_object* v_xs_1194_ = _args[2];
lean_object* v_allIndVals_1195_ = _args[3];
lean_object* v_ctx_1196_ = _args[4];
lean_object* v_inst_1197_ = _args[5];
lean_object* v_R_1198_ = _args[6];
lean_object* v_a_1199_ = _args[7];
lean_object* v_b_1200_ = _args[8];
lean_object* v_c_1201_ = _args[9];
lean_object* v___y_1202_ = _args[10];
lean_object* v___y_1203_ = _args[11];
lean_object* v___y_1204_ = _args[12];
lean_object* v___y_1205_ = _args[13];
lean_object* v___y_1206_ = _args[14];
lean_object* v___y_1207_ = _args[15];
lean_object* v___y_1208_ = _args[16];
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3(v_upperBound_1192_, v___x_1193_, v_xs_1194_, v_allIndVals_1195_, v_ctx_1196_, v_inst_1197_, v_R_1198_, v_a_1199_, v_b_1200_, v_c_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec_ref(v_ctx_1196_);
lean_dec_ref(v_allIndVals_1195_);
lean_dec_ref(v_xs_1194_);
lean_dec(v___x_1193_);
lean_dec(v_upperBound_1192_);
return v_res_1209_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4(lean_object* v_upperBound_1210_, lean_object* v_inst_1211_, lean_object* v_R_1212_, lean_object* v_a_1213_, lean_object* v_b_1214_, lean_object* v_c_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_upperBound_1210_, v_a_1213_, v_b_1214_, v___y_1220_);
return v___x_1223_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1210_ = stack[0].m_obj;
lean_object* v_a_1213_ = stack[3].m_obj;
lean_object* v_b_1214_ = stack[4].m_obj;
lean_object* v___y_1216_ = stack[6].m_obj;
lean_object* v___y_1217_ = stack[7].m_obj;
lean_object* v___y_1218_ = stack[8].m_obj;
lean_object* v___y_1219_ = stack[9].m_obj;
lean_object* v___y_1220_ = stack[10].m_obj;
lean_object* v___y_1221_ = stack[11].m_obj;
lean_object* v_res_1224_;
v_res_1224_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4(v_upperBound_1210_, lean_box(0), lean_box(0), v_a_1213_, v_b_1214_, lean_box(0), v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
stack->m_obj
 = v_res_1224_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___boxed(lean_object* v_upperBound_1225_, lean_object* v_inst_1226_, lean_object* v_R_1227_, lean_object* v_a_1228_, lean_object* v_b_1229_, lean_object* v_c_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4(v_upperBound_1225_, v_inst_1226_, v_R_1227_, v_a_1228_, v_b_1229_, v_c_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v_upperBound_1225_);
return v_res_1238_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(lean_object* v_indVal_1239_, lean_object* v_allIndVals_1240_, lean_object* v_ctx_1241_, lean_object* v_as_1242_, lean_object* v_as_x27_1243_, lean_object* v_b_1244_, lean_object* v_a_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(v_indVal_1239_, v_allIndVals_1240_, v_ctx_1241_, v_as_x27_1243_, v_b_1244_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_1239_ = stack[0].m_obj;
lean_object* v_allIndVals_1240_ = stack[1].m_obj;
lean_object* v_ctx_1241_ = stack[2].m_obj;
lean_object* v_as_1242_ = stack[3].m_obj;
lean_object* v_as_x27_1243_ = stack[4].m_obj;
lean_object* v_b_1244_ = stack[5].m_obj;
lean_object* v___y_1246_ = stack[7].m_obj;
lean_object* v___y_1247_ = stack[8].m_obj;
lean_object* v___y_1248_ = stack[9].m_obj;
lean_object* v___y_1249_ = stack[10].m_obj;
lean_object* v___y_1250_ = stack[11].m_obj;
lean_object* v___y_1251_ = stack[12].m_obj;
lean_object* v_res_1254_;
v_res_1254_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(v_indVal_1239_, v_allIndVals_1240_, v_ctx_1241_, v_as_1242_, v_as_x27_1243_, v_b_1244_, lean_box(0), v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
stack->m_obj
 = v_res_1254_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___boxed(lean_object* v_indVal_1255_, lean_object* v_allIndVals_1256_, lean_object* v_ctx_1257_, lean_object* v_as_1258_, lean_object* v_as_x27_1259_, lean_object* v_b_1260_, lean_object* v_a_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(v_indVal_1255_, v_allIndVals_1256_, v_ctx_1257_, v_as_1258_, v_as_x27_1259_, v_b_1260_, v_a_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v_as_x27_1259_);
lean_dec(v_as_1258_);
return v_res_1269_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1270_, lean_object* v_msg_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v_msg_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1271_ = stack[1].m_obj;
lean_object* v___y_1272_ = stack[2].m_obj;
lean_object* v___y_1273_ = stack[3].m_obj;
lean_object* v___y_1274_ = stack[4].m_obj;
lean_object* v___y_1275_ = stack[5].m_obj;
lean_object* v___y_1276_ = stack[6].m_obj;
lean_object* v___y_1277_ = stack[7].m_obj;
lean_object* v_res_1280_;
v_res_1280_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0(lean_box(0), v_msg_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
stack->m_obj
 = v_res_1280_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1281_, lean_object* v_msg_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0(v_00_u03b1_1281_, v_msg_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1290_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1291_, lean_object* v_macroStack_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1291_, v_macroStack_1292_, v___y_1297_);
return v___x_1300_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1291_ = stack[0].m_obj;
lean_object* v_macroStack_1292_ = stack[1].m_obj;
lean_object* v___y_1293_ = stack[2].m_obj;
lean_object* v___y_1294_ = stack[3].m_obj;
lean_object* v___y_1295_ = stack[4].m_obj;
lean_object* v___y_1296_ = stack[5].m_obj;
lean_object* v___y_1297_ = stack[6].m_obj;
lean_object* v___y_1298_ = stack[7].m_obj;
lean_object* v_res_1301_;
v_res_1301_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3(v_msgData_1291_, v_macroStack_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
stack->m_obj
 = v_res_1301_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1302_, lean_object* v_macroStack_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3(v_msgData_1302_, v_macroStack_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1311_;
}
}
lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch(lean_object* v_ctx_1325_, lean_object* v_header_1326_, lean_object* v_indVal_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1335_; 
lean_inc_ref(v_indVal_1327_);
v___x_1335_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_1326_, v_indVal_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1337_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(v_ctx_1325_, v_indVal_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1368_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1368_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1368_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_ref_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; size_t v_sz_1351_; size_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v_ref_1342_ = lean_ctor_get(v_a_1332_, 2);
v___x_1343_ = 0;
v___x_1344_ = l_Lean_SourceInfo_fromRef(v_ref_1342_, v___x_1343_);
v___x_1345_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0));
v___x_1346_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1));
lean_inc_n(v___x_1344_, 6);
v___x_1347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1344_);
lean_ctor_set(v___x_1347_, 1, v___x_1345_);
v___x_1348_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_1349_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_1350_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1344_);
lean_ctor_set(v___x_1350_, 1, v___x_1348_);
lean_ctor_set(v___x_1350_, 2, v___x_1349_);
v_sz_1351_ = lean_array_size(v_a_1336_);
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_1351_, v___x_1352_, v_a_1336_);
v___x_1354_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8);
v___x_1355_ = l_Lean_mkSepArray(v___x_1353_, v___x_1354_);
lean_dec_ref(v___x_1353_);
v___x_1356_ = l_Array_append___redArg(v___x_1349_, v___x_1355_);
lean_dec_ref(v___x_1355_);
v___x_1357_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1344_);
lean_ctor_set(v___x_1357_, 1, v___x_1348_);
lean_ctor_set(v___x_1357_, 2, v___x_1356_);
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2));
v___x_1359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1344_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4));
v___x_1361_ = l_Array_append___redArg(v___x_1349_, v_a_1338_);
lean_dec(v_a_1338_);
v___x_1362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1344_);
lean_ctor_set(v___x_1362_, 1, v___x_1348_);
lean_ctor_set(v___x_1362_, 2, v___x_1361_);
v___x_1363_ = l_Lean_Syntax_node1(v___x_1344_, v___x_1360_, v___x_1362_);
lean_inc_ref(v___x_1350_);
v___x_1364_ = l_Lean_Syntax_node6(v___x_1344_, v___x_1346_, v___x_1347_, v___x_1350_, v___x_1350_, v___x_1357_, v___x_1359_, v___x_1363_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1364_);
v___x_1366_ = v___x_1340_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v_a_1336_);
v_a_1369_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1337_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1337_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v_indVal_1327_);
lean_dec_ref(v_ctx_1325_);
v_a_1377_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1335_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1335_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Hashable_mkMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1325_ = stack[0].m_obj;
lean_object* v_header_1326_ = stack[1].m_obj;
lean_object* v_indVal_1327_ = stack[2].m_obj;
lean_object* v_a_1328_ = stack[3].m_obj;
lean_object* v_a_1329_ = stack[4].m_obj;
lean_object* v_a_1330_ = stack[5].m_obj;
lean_object* v_a_1331_ = stack[6].m_obj;
lean_object* v_a_1332_ = stack[7].m_obj;
lean_object* v_a_1333_ = stack[8].m_obj;
lean_object* v_res_1385_;
v_res_1385_ = l_Lean_Elab_Deriving_Hashable_mkMatch(v_ctx_1325_, v_header_1326_, v_indVal_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
stack->m_obj
 = v_res_1385_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___boxed(lean_object* v_ctx_1386_, lean_object* v_header_1387_, lean_object* v_indVal_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Elab_Deriving_Hashable_mkMatch(v_ctx_1386_, v_header_1387_, v_indVal_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
return v_res_1396_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14));
v___x_1437_ = l_String_toRawSubstring_x27(v___x_1436_);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28));
v___x_1469_ = l_String_toRawSubstring_x27(v___x_1468_);
return v___x_1469_;
}
}
lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction(lean_object* v_ctx_1515_, lean_object* v_i_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_typeInfos_1524_; lean_object* v_auxFunNames_1525_; uint8_t v_usePartial_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v_auxFunName_1529_; lean_object* v_indVal_1530_; lean_object* v___x_1531_; 
v_typeInfos_1524_ = lean_ctor_get(v_ctx_1515_, 1);
v_auxFunNames_1525_ = lean_ctor_get(v_ctx_1515_, 2);
v_usePartial_1526_ = lean_ctor_get_uint8(v_ctx_1515_, sizeof(void*)*3);
v___x_1527_ = lean_box(0);
v___x_1528_ = l_Lean_instInhabitedInductiveVal_default;
v_auxFunName_1529_ = lean_array_get(v___x_1527_, v_auxFunNames_1525_, v_i_1516_);
v_indVal_1530_ = lean_array_get_borrowed(v___x_1528_, v_typeInfos_1524_, v_i_1516_);
lean_inc(v_indVal_1530_);
v___x_1531_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader(v_indVal_1530_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1685_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1534_ = v___x_1531_;
v_isShared_1535_ = v_isSharedCheck_1685_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1531_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1685_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v_body_1537_; lean_object* v___y_1538_; lean_object* v___x_1668_; 
lean_inc(v_indVal_1530_);
lean_inc(v_a_1532_);
lean_inc_ref(v_ctx_1515_);
v___x_1668_ = l_Lean_Elab_Deriving_Hashable_mkMatch(v_ctx_1515_, v_a_1532_, v_indVal_1530_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
if (lean_obj_tag(v___x_1668_) == 0)
{
if (v_usePartial_1526_ == 0)
{
lean_object* v_a_1669_; 
lean_dec_ref(v_ctx_1515_);
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v_body_1537_ = v_a_1669_;
v___y_1538_ = v_a_1521_;
goto v___jp_1536_;
}
else
{
lean_object* v_a_1670_; lean_object* v_argNames_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_a_1670_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1668_, 1);
v_argNames_1671_ = lean_ctor_get(v_a_1532_, 1);
v___x_1672_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1));
lean_inc_ref(v_argNames_1671_);
v___x_1673_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_1515_, v___x_1672_, v_argNames_1671_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec_ref(v_ctx_1515_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v___x_1675_ = l_Lean_Elab_Deriving_mkLet(v_a_1674_, v_a_1670_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec(v_a_1674_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v_body_1537_ = v_a_1676_;
v___y_1538_ = v_a_1521_;
goto v___jp_1536_;
}
else
{
lean_del_object(v___x_1534_);
lean_dec(v_a_1532_);
lean_dec(v_auxFunName_1529_);
return v___x_1675_;
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec(v_a_1670_);
lean_del_object(v___x_1534_);
lean_dec(v_a_1532_);
lean_dec(v_auxFunName_1529_);
v_a_1677_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1673_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1673_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
else
{
lean_del_object(v___x_1534_);
lean_dec(v_a_1532_);
lean_dec(v_auxFunName_1529_);
lean_dec_ref(v_ctx_1515_);
return v___x_1668_;
}
v___jp_1536_:
{
if (v_usePartial_1526_ == 0)
{
lean_object* v_toCold_1539_; lean_object* v_binders_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1606_; 
v_toCold_1539_ = lean_ctor_get(v___y_1538_, 0);
v_binders_1540_ = lean_ctor_get(v_a_1532_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_a_1532_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; 
v_unused_1607_ = lean_ctor_get(v_a_1532_, 3);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_a_1532_, 2);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_a_1532_, 1);
lean_dec(v_unused_1609_);
v___x_1542_ = v_a_1532_;
v_isShared_1543_ = v_isSharedCheck_1606_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_binders_1540_);
lean_dec(v_a_1532_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1606_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_ref_1544_; lean_object* v_quotContext_1545_; lean_object* v_currMacroScope_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v_ref_1544_ = lean_ctor_get(v___y_1538_, 2);
v_quotContext_1545_ = lean_ctor_get(v_toCold_1539_, 8);
v_currMacroScope_1546_ = lean_ctor_get(v_toCold_1539_, 9);
v___x_1547_ = l_Lean_SourceInfo_fromRef(v_ref_1544_, v_usePartial_1526_);
v___x_1548_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1));
v___x_1549_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3));
v___x_1550_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_1551_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
lean_inc_n(v___x_1547_, 4);
v___x_1552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1547_);
lean_ctor_set(v___x_1552_, 1, v___x_1550_);
lean_ctor_set(v___x_1552_, 2, v___x_1551_);
v___x_1553_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5));
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6));
v___x_1555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1547_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8));
v___x_1557_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10));
lean_inc_ref(v___x_1552_);
v___x_1558_ = l_Lean_Syntax_node1(v___x_1547_, v___x_1557_, v___x_1552_);
v___x_1559_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13));
v___x_1560_ = lean_obj_once(&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15, &l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15_once, _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15);
v___x_1561_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__16));
lean_inc(v_currMacroScope_1546_);
lean_inc(v_quotContext_1545_);
v___x_1562_ = l_Lean_addMacroScope(v_quotContext_1545_, v___x_1561_, v_currMacroScope_1546_);
v___x_1563_ = lean_box(0);
if (v_isShared_1543_ == 0)
{
lean_ctor_set_tag(v___x_1542_, 3);
lean_ctor_set(v___x_1542_, 3, v___x_1563_);
lean_ctor_set(v___x_1542_, 2, v___x_1562_);
lean_ctor_set(v___x_1542_, 1, v___x_1560_);
lean_ctor_set(v___x_1542_, 0, v___x_1547_);
v___x_1565_ = v___x_1542_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
lean_inc_ref_n(v___x_1552_, 11);
lean_inc_n(v___x_1547_, 19);
v___x_1566_ = l_Lean_Syntax_node2(v___x_1547_, v___x_1559_, v___x_1565_, v___x_1552_);
v___x_1567_ = l_Lean_Syntax_node2(v___x_1547_, v___x_1556_, v___x_1558_, v___x_1566_);
v___x_1568_ = l_Lean_Syntax_node1(v___x_1547_, v___x_1550_, v___x_1567_);
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__17));
v___x_1570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1547_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = l_Lean_Syntax_node3(v___x_1547_, v___x_1553_, v___x_1555_, v___x_1568_, v___x_1570_);
v___x_1572_ = l_Lean_Syntax_node1(v___x_1547_, v___x_1550_, v___x_1571_);
v___x_1573_ = l_Lean_Syntax_node7(v___x_1547_, v___x_1549_, v___x_1552_, v___x_1572_, v___x_1552_, v___x_1552_, v___x_1552_, v___x_1552_, v___x_1552_);
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19));
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20));
v___x_1576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1547_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22));
v___x_1578_ = l_Lean_mkIdent(v_auxFunName_1529_);
v___x_1579_ = l_Lean_Syntax_node2(v___x_1547_, v___x_1577_, v___x_1578_, v___x_1552_);
v___x_1580_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24));
v___x_1581_ = l_Array_append___redArg(v___x_1551_, v_binders_1540_);
lean_dec_ref(v_binders_1540_);
v___x_1582_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1547_);
lean_ctor_set(v___x_1582_, 1, v___x_1550_);
lean_ctor_set(v___x_1582_, 2, v___x_1581_);
v___x_1583_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26));
v___x_1584_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27));
v___x_1585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1547_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_obj_once(&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29, &l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29_once, _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29);
v___x_1587_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30));
lean_inc(v_currMacroScope_1546_);
lean_inc(v_quotContext_1545_);
v___x_1588_ = l_Lean_addMacroScope(v_quotContext_1545_, v___x_1587_, v_currMacroScope_1546_);
v___x_1589_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35));
v___x_1590_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1547_);
lean_ctor_set(v___x_1590_, 1, v___x_1586_);
lean_ctor_set(v___x_1590_, 2, v___x_1588_);
lean_ctor_set(v___x_1590_, 3, v___x_1589_);
v___x_1591_ = l_Lean_Syntax_node2(v___x_1547_, v___x_1583_, v___x_1585_, v___x_1590_);
v___x_1592_ = l_Lean_Syntax_node1(v___x_1547_, v___x_1550_, v___x_1591_);
v___x_1593_ = l_Lean_Syntax_node2(v___x_1547_, v___x_1580_, v___x_1582_, v___x_1592_);
v___x_1594_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37));
v___x_1595_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38));
v___x_1596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1547_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41));
v___x_1598_ = l_Lean_Syntax_node2(v___x_1547_, v___x_1597_, v___x_1552_, v___x_1552_);
v___x_1599_ = l_Lean_Syntax_node4(v___x_1547_, v___x_1594_, v___x_1596_, v_body_1537_, v___x_1598_, v___x_1552_);
v___x_1600_ = l_Lean_Syntax_node5(v___x_1547_, v___x_1574_, v___x_1576_, v___x_1579_, v___x_1593_, v___x_1599_, v___x_1552_);
v___x_1601_ = l_Lean_Syntax_node2(v___x_1547_, v___x_1548_, v___x_1573_, v___x_1600_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1601_);
v___x_1603_ = v___x_1534_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
lean_object* v_toCold_1610_; lean_object* v_binders_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1664_; 
v_toCold_1610_ = lean_ctor_get(v___y_1538_, 0);
v_binders_1611_ = lean_ctor_get(v_a_1532_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_a_1532_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; lean_object* v_unused_1666_; lean_object* v_unused_1667_; 
v_unused_1665_ = lean_ctor_get(v_a_1532_, 3);
lean_dec(v_unused_1665_);
v_unused_1666_ = lean_ctor_get(v_a_1532_, 2);
lean_dec(v_unused_1666_);
v_unused_1667_ = lean_ctor_get(v_a_1532_, 1);
lean_dec(v_unused_1667_);
v___x_1613_ = v_a_1532_;
v_isShared_1614_ = v_isSharedCheck_1664_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_binders_1611_);
lean_dec(v_a_1532_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1664_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_ref_1615_; lean_object* v_quotContext_1616_; lean_object* v_currMacroScope_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
v_ref_1615_ = lean_ctor_get(v___y_1538_, 2);
v_quotContext_1616_ = lean_ctor_get(v_toCold_1610_, 8);
v_currMacroScope_1617_ = lean_ctor_get(v_toCold_1610_, 9);
v___x_1618_ = 0;
v___x_1619_ = l_Lean_SourceInfo_fromRef(v_ref_1615_, v___x_1618_);
v___x_1620_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1));
v___x_1621_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3));
v___x_1622_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_1623_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
lean_inc_n(v___x_1619_, 10);
v___x_1624_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1619_);
lean_ctor_set(v___x_1624_, 1, v___x_1622_);
lean_ctor_set(v___x_1624_, 2, v___x_1623_);
v___x_1625_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42));
v___x_1626_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43));
v___x_1627_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1619_);
lean_ctor_set(v___x_1627_, 1, v___x_1625_);
v___x_1628_ = l_Lean_Syntax_node1(v___x_1619_, v___x_1626_, v___x_1627_);
v___x_1629_ = l_Lean_Syntax_node1(v___x_1619_, v___x_1622_, v___x_1628_);
lean_inc_ref_n(v___x_1624_, 7);
v___x_1630_ = l_Lean_Syntax_node7(v___x_1619_, v___x_1621_, v___x_1624_, v___x_1624_, v___x_1624_, v___x_1624_, v___x_1624_, v___x_1624_, v___x_1629_);
v___x_1631_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19));
v___x_1632_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20));
v___x_1633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1619_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22));
v___x_1635_ = l_Lean_mkIdent(v_auxFunName_1529_);
v___x_1636_ = l_Lean_Syntax_node2(v___x_1619_, v___x_1634_, v___x_1635_, v___x_1624_);
v___x_1637_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24));
v___x_1638_ = l_Array_append___redArg(v___x_1623_, v_binders_1611_);
lean_dec_ref(v_binders_1611_);
v___x_1639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1619_);
lean_ctor_set(v___x_1639_, 1, v___x_1622_);
lean_ctor_set(v___x_1639_, 2, v___x_1638_);
v___x_1640_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26));
v___x_1641_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27));
v___x_1642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1619_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = lean_obj_once(&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29, &l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29_once, _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29);
v___x_1644_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30));
lean_inc(v_currMacroScope_1617_);
lean_inc(v_quotContext_1616_);
v___x_1645_ = l_Lean_addMacroScope(v_quotContext_1616_, v___x_1644_, v_currMacroScope_1617_);
v___x_1646_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__46));
if (v_isShared_1614_ == 0)
{
lean_ctor_set_tag(v___x_1613_, 3);
lean_ctor_set(v___x_1613_, 3, v___x_1646_);
lean_ctor_set(v___x_1613_, 2, v___x_1645_);
lean_ctor_set(v___x_1613_, 1, v___x_1643_);
lean_ctor_set(v___x_1613_, 0, v___x_1619_);
v___x_1648_ = v___x_1613_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1663_, 3, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
lean_inc_n(v___x_1619_, 7);
v___x_1649_ = l_Lean_Syntax_node2(v___x_1619_, v___x_1640_, v___x_1642_, v___x_1648_);
v___x_1650_ = l_Lean_Syntax_node1(v___x_1619_, v___x_1622_, v___x_1649_);
v___x_1651_ = l_Lean_Syntax_node2(v___x_1619_, v___x_1637_, v___x_1639_, v___x_1650_);
v___x_1652_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37));
v___x_1653_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38));
v___x_1654_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1619_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41));
lean_inc_ref_n(v___x_1624_, 3);
v___x_1656_ = l_Lean_Syntax_node2(v___x_1619_, v___x_1655_, v___x_1624_, v___x_1624_);
v___x_1657_ = l_Lean_Syntax_node4(v___x_1619_, v___x_1652_, v___x_1654_, v_body_1537_, v___x_1656_, v___x_1624_);
v___x_1658_ = l_Lean_Syntax_node5(v___x_1619_, v___x_1631_, v___x_1633_, v___x_1636_, v___x_1651_, v___x_1657_, v___x_1624_);
v___x_1659_ = l_Lean_Syntax_node2(v___x_1619_, v___x_1620_, v___x_1630_, v___x_1658_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1659_);
v___x_1661_ = v___x_1534_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_auxFunName_1529_);
lean_dec_ref(v_ctx_1515_);
v_a_1686_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1531_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1531_);
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
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Hashable_mkAuxFunction_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1515_ = stack[0].m_obj;
lean_object* v_i_1516_ = stack[1].m_obj;
lean_object* v_a_1517_ = stack[2].m_obj;
lean_object* v_a_1518_ = stack[3].m_obj;
lean_object* v_a_1519_ = stack[4].m_obj;
lean_object* v_a_1520_ = stack[5].m_obj;
lean_object* v_a_1521_ = stack[6].m_obj;
lean_object* v_a_1522_ = stack[7].m_obj;
lean_object* v_res_1694_;
v_res_1694_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction(v_ctx_1515_, v_i_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
stack->m_obj
 = v_res_1694_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___boxed(lean_object* v_ctx_1695_, lean_object* v_i_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction(v_ctx_1695_, v_i_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_i_1696_);
return v_res_1704_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(lean_object* v_upperBound_1705_, lean_object* v_ctx_1706_, lean_object* v_a_1707_, lean_object* v_b_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_nat_dec_lt(v_a_1707_, v_upperBound_1705_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec(v_a_1707_);
lean_dec_ref(v_ctx_1706_);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_b_1708_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; 
lean_inc_ref(v_ctx_1706_);
v___x_1718_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction(v_ctx_1706_, v_a_1707_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = lean_array_push(v_b_1708_, v_a_1719_);
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_nat_add(v_a_1707_, v___x_1721_);
lean_dec(v_a_1707_);
v_a_1707_ = v___x_1722_;
v_b_1708_ = v___x_1720_;
goto _start;
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v_b_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_ctx_1706_);
v_a_1724_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1718_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1718_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1705_ = stack[0].m_obj;
lean_object* v_ctx_1706_ = stack[1].m_obj;
lean_object* v_a_1707_ = stack[2].m_obj;
lean_object* v_b_1708_ = stack[3].m_obj;
lean_object* v___y_1709_ = stack[4].m_obj;
lean_object* v___y_1710_ = stack[5].m_obj;
lean_object* v___y_1711_ = stack[6].m_obj;
lean_object* v___y_1712_ = stack[7].m_obj;
lean_object* v___y_1713_ = stack[8].m_obj;
lean_object* v___y_1714_ = stack[9].m_obj;
lean_object* v_res_1732_;
v_res_1732_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v_upperBound_1705_, v_ctx_1706_, v_a_1707_, v_b_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
stack->m_obj
 = v_res_1732_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg___boxed(lean_object* v_upperBound_1733_, lean_object* v_ctx_1734_, lean_object* v_a_1735_, lean_object* v_b_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v_upperBound_1733_, v_ctx_1734_, v_a_1735_, v_b_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_upperBound_1733_);
return v_res_1744_;
}
}
lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs(lean_object* v_ctx_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_typeInfos_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v_auxDefs_1763_; lean_object* v___x_1764_; 
v_typeInfos_1760_ = lean_ctor_get(v_ctx_1752_, 1);
v___x_1761_ = lean_array_get_size(v_typeInfos_1760_);
v___x_1762_ = lean_unsigned_to_nat(0u);
v_auxDefs_1763_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1));
v___x_1764_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v___x_1761_, v_ctx_1752_, v___x_1762_, v_auxDefs_1763_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1785_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1785_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1785_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_ref_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
v_ref_1769_ = lean_ctor_get(v_a_1757_, 2);
v___x_1770_ = 0;
v___x_1771_ = l_Lean_SourceInfo_fromRef(v_ref_1769_, v___x_1770_);
v___x_1772_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0));
v___x_1773_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1));
lean_inc_n(v___x_1771_, 3);
v___x_1774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1771_);
lean_ctor_set(v___x_1774_, 1, v___x_1772_);
v___x_1775_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_1776_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_1777_ = l_Array_append___redArg(v___x_1776_, v_a_1765_);
lean_dec(v_a_1765_);
v___x_1778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1771_);
lean_ctor_set(v___x_1778_, 1, v___x_1775_);
lean_ctor_set(v___x_1778_, 2, v___x_1777_);
v___x_1779_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2));
v___x_1780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1771_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = l_Lean_Syntax_node3(v___x_1771_, v___x_1773_, v___x_1774_, v___x_1778_, v___x_1780_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1781_);
v___x_1783_ = v___x_1767_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_a_1786_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1764_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1764_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Hashable_mkHashFuncs_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1752_ = stack[0].m_obj;
lean_object* v_a_1753_ = stack[1].m_obj;
lean_object* v_a_1754_ = stack[2].m_obj;
lean_object* v_a_1755_ = stack[3].m_obj;
lean_object* v_a_1756_ = stack[4].m_obj;
lean_object* v_a_1757_ = stack[5].m_obj;
lean_object* v_a_1758_ = stack[6].m_obj;
lean_object* v_res_1794_;
v_res_1794_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs(v_ctx_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
stack->m_obj
 = v_res_1794_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs___boxed(lean_object* v_ctx_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs(v_ctx_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
return v_res_1803_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0(lean_object* v_upperBound_1804_, lean_object* v_ctx_1805_, lean_object* v_inst_1806_, lean_object* v_R_1807_, lean_object* v_a_1808_, lean_object* v_b_1809_, lean_object* v_c_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v_upperBound_1804_, v_ctx_1805_, v_a_1808_, v_b_1809_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1804_ = stack[0].m_obj;
lean_object* v_ctx_1805_ = stack[1].m_obj;
lean_object* v_a_1808_ = stack[4].m_obj;
lean_object* v_b_1809_ = stack[5].m_obj;
lean_object* v___y_1811_ = stack[7].m_obj;
lean_object* v___y_1812_ = stack[8].m_obj;
lean_object* v___y_1813_ = stack[9].m_obj;
lean_object* v___y_1814_ = stack[10].m_obj;
lean_object* v___y_1815_ = stack[11].m_obj;
lean_object* v___y_1816_ = stack[12].m_obj;
lean_object* v_res_1819_;
v_res_1819_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0(v_upperBound_1804_, v_ctx_1805_, lean_box(0), lean_box(0), v_a_1808_, v_b_1809_, lean_box(0), v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
stack->m_obj
 = v_res_1819_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___boxed(lean_object* v_upperBound_1820_, lean_object* v_ctx_1821_, lean_object* v_inst_1822_, lean_object* v_R_1823_, lean_object* v_a_1824_, lean_object* v_b_1825_, lean_object* v_c_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0(v_upperBound_1820_, v_ctx_1821_, v_inst_1822_, v_R_1823_, v_a_1824_, v_b_1825_, v_c_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v_upperBound_1820_);
return v_res_1834_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1835_; double v___x_1836_; 
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = lean_float_of_nat(v___x_1835_);
return v___x_1836_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(lean_object* v_cls_1839_, lean_object* v_msg_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_ref_1846_; lean_object* v___x_1847_; lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1893_; 
v_ref_1846_ = lean_ctor_get(v___y_1843_, 2);
v___x_1847_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msg_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1893_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1893_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v_traceState_1853_; lean_object* v_env_1854_; lean_object* v_nextMacroScope_1855_; lean_object* v_ngen_1856_; lean_object* v_auxDeclNGen_1857_; lean_object* v_cache_1858_; lean_object* v_recordedDeps_1859_; lean_object* v_messages_1860_; lean_object* v_infoState_1861_; lean_object* v_snapshotTasks_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1892_; 
v___x_1852_ = lean_st_ref_take(v___y_1844_);
v_traceState_1853_ = lean_ctor_get(v___x_1852_, 4);
v_env_1854_ = lean_ctor_get(v___x_1852_, 0);
v_nextMacroScope_1855_ = lean_ctor_get(v___x_1852_, 1);
v_ngen_1856_ = lean_ctor_get(v___x_1852_, 2);
v_auxDeclNGen_1857_ = lean_ctor_get(v___x_1852_, 3);
v_cache_1858_ = lean_ctor_get(v___x_1852_, 5);
v_recordedDeps_1859_ = lean_ctor_get(v___x_1852_, 6);
v_messages_1860_ = lean_ctor_get(v___x_1852_, 7);
v_infoState_1861_ = lean_ctor_get(v___x_1852_, 8);
v_snapshotTasks_1862_ = lean_ctor_get(v___x_1852_, 9);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1864_ = v___x_1852_;
v_isShared_1865_ = v_isSharedCheck_1892_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_snapshotTasks_1862_);
lean_inc(v_infoState_1861_);
lean_inc(v_messages_1860_);
lean_inc(v_recordedDeps_1859_);
lean_inc(v_cache_1858_);
lean_inc(v_traceState_1853_);
lean_inc(v_auxDeclNGen_1857_);
lean_inc(v_ngen_1856_);
lean_inc(v_nextMacroScope_1855_);
lean_inc(v_env_1854_);
lean_dec(v___x_1852_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1892_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
uint64_t v_tid_1866_; lean_object* v_traces_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1891_; 
v_tid_1866_ = lean_ctor_get_uint64(v_traceState_1853_, sizeof(void*)*1);
v_traces_1867_ = lean_ctor_get(v_traceState_1853_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_traceState_1853_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1869_ = v_traceState_1853_;
v_isShared_1870_ = v_isSharedCheck_1891_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_traces_1867_);
lean_dec(v_traceState_1853_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1891_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; double v___x_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_box(0);
v___x_1873_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0);
v___x_1874_ = 0;
v___x_1875_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18));
v___x_1876_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1876_, 0, v_cls_1839_);
lean_ctor_set(v___x_1876_, 1, v___x_1872_);
lean_ctor_set(v___x_1876_, 2, v___x_1875_);
lean_ctor_set_float(v___x_1876_, sizeof(void*)*3, v___x_1873_);
lean_ctor_set_float(v___x_1876_, sizeof(void*)*3 + 8, v___x_1873_);
lean_ctor_set_uint8(v___x_1876_, sizeof(void*)*3 + 16, v___x_1874_);
v___x_1877_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__1));
v___x_1878_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v_a_1848_);
lean_ctor_set(v___x_1878_, 2, v___x_1877_);
lean_inc(v_ref_1846_);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v_ref_1846_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = l_Lean_PersistentArray_push___redArg(v_traces_1867_, v___x_1879_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1880_);
v___x_1882_ = v___x_1869_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1880_);
lean_ctor_set_uint64(v_reuseFailAlloc_1890_, sizeof(void*)*1, v_tid_1866_);
v___x_1882_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1884_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 4, v___x_1882_);
v___x_1884_ = v___x_1864_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_env_1854_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_nextMacroScope_1855_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_ngen_1856_);
lean_ctor_set(v_reuseFailAlloc_1889_, 3, v_auxDeclNGen_1857_);
lean_ctor_set(v_reuseFailAlloc_1889_, 4, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1889_, 5, v_cache_1858_);
lean_ctor_set(v_reuseFailAlloc_1889_, 6, v_recordedDeps_1859_);
lean_ctor_set(v_reuseFailAlloc_1889_, 7, v_messages_1860_);
lean_ctor_set(v_reuseFailAlloc_1889_, 8, v_infoState_1861_);
lean_ctor_set(v_reuseFailAlloc_1889_, 9, v_snapshotTasks_1862_);
v___x_1884_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_st_ref_put(v___y_1844_, v___x_1884_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1871_);
v___x_1887_ = v___x_1850_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1871_);
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
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1839_ = stack[0].m_obj;
lean_object* v_msg_1840_ = stack[1].m_obj;
lean_object* v___y_1841_ = stack[2].m_obj;
lean_object* v___y_1842_ = stack[3].m_obj;
lean_object* v___y_1843_ = stack[4].m_obj;
lean_object* v___y_1844_ = stack[5].m_obj;
lean_object* v_res_1894_;
v_res_1894_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(v_cls_1839_, v_msg_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
stack->m_obj
 = v_res_1894_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_1895_, lean_object* v_msg_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(v_cls_1895_, v_msg_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0(lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
if (lean_obj_tag(v_a_1903_) == 0)
{
lean_object* v___x_1905_; 
v___x_1905_ = l_List_reverse___redArg(v_a_1904_);
return v___x_1905_;
}
else
{
lean_object* v_head_1906_; lean_object* v_tail_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1916_; 
v_head_1906_ = lean_ctor_get(v_a_1903_, 0);
v_tail_1907_ = lean_ctor_get(v_a_1903_, 1);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_a_1903_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1909_ = v_a_1903_;
v_isShared_1910_ = v_isSharedCheck_1916_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_tail_1907_);
lean_inc(v_head_1906_);
lean_dec(v_a_1903_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1916_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1911_ = l_Lean_MessageData_ofSyntax(v_head_1906_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v_a_1904_);
lean_ctor_set(v___x_1909_, 0, v___x_1911_);
v___x_1913_ = v___x_1909_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_a_1904_);
v___x_1913_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
v_a_1903_ = v_tail_1907_;
v_a_1904_ = v___x_1913_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1));
v___x_1926_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3));
v___x_1927_ = l_Lean_Name_append(v___x_1926_, v___x_1925_);
return v___x_1927_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__5));
v___x_1930_ = l_Lean_stringToMessageData(v___x_1929_);
return v___x_1930_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds(lean_object* v_declName_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1939_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1));
v___x_1940_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36));
v___x_1941_ = 1;
lean_inc(v_declName_1931_);
v___x_1942_ = l_Lean_Elab_Deriving_mkContext(v___x_1939_, v___x_1940_, v_declName_1931_, v___x_1941_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc_n(v_a_1943_, 2);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs(v_a_1943_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v___x_1946_ = lean_unsigned_to_nat(1u);
v___x_1947_ = lean_mk_empty_array_with_capacity(v___x_1946_);
lean_inc_ref(v___x_1947_);
v___x_1948_ = lean_array_push(v___x_1947_, v_declName_1931_);
v___x_1949_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_1943_, v___x_1939_, v___x_1948_, v___x_1941_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
lean_dec_ref(v___x_1948_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_toCold_1950_; lean_object* v_options_1951_; lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1992_; 
v_toCold_1950_ = lean_ctor_get(v_a_1936_, 0);
v_options_1951_ = lean_ctor_get(v_toCold_1950_, 2);
v_a_1952_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1954_ = v___x_1949_;
v_isShared_1955_ = v_isSharedCheck_1992_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1949_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1992_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v_inheritedTraceOptions_1956_; uint8_t v_hasTrace_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v_inheritedTraceOptions_1956_ = lean_ctor_get(v_toCold_1950_, 11);
v_hasTrace_1957_ = lean_ctor_get_uint8(v_options_1951_, sizeof(void*)*1);
v___x_1958_ = lean_array_push(v___x_1947_, v_a_1945_);
v___x_1959_ = l_Array_append___redArg(v___x_1958_, v_a_1952_);
lean_dec(v_a_1952_);
if (v_hasTrace_1957_ == 0)
{
lean_object* v___x_1961_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1959_);
v___x_1961_ = v___x_1954_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1963_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1));
v___x_1964_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4_once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4);
v___x_1965_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1956_, v_options_1951_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1967_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1959_);
v___x_1967_ = v___x_1954_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1959_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_del_object(v___x_1954_);
v___x_1969_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6_once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6);
lean_inc_ref(v___x_1959_);
v___x_1970_ = lean_array_to_list(v___x_1959_);
v___x_1971_ = lean_box(0);
v___x_1972_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0(v___x_1970_, v___x_1971_);
v___x_1973_ = l_Lean_MessageData_ofList(v___x_1972_);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1969_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(v___x_1963_, v___x_1974_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v___x_1975_, 0);
lean_dec(v_unused_1983_);
v___x_1977_ = v___x_1975_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_dec(v___x_1975_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1959_);
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1959_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v___x_1959_);
v_a_1984_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1975_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1975_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v___x_1947_);
lean_dec(v_a_1945_);
v_a_1993_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1949_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1949_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_a_1943_);
lean_dec(v_declName_1931_);
v_a_2001_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1944_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1944_);
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
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_declName_1931_);
v_a_2009_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1942_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1942_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1931_ = stack[0].m_obj;
lean_object* v_a_1932_ = stack[1].m_obj;
lean_object* v_a_1933_ = stack[2].m_obj;
lean_object* v_a_1934_ = stack[3].m_obj;
lean_object* v_a_1935_ = stack[4].m_obj;
lean_object* v_a_1936_ = stack[5].m_obj;
lean_object* v_a_1937_ = stack[6].m_obj;
lean_object* v_res_2017_;
v_res_2017_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds(v_declName_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
stack->m_obj
 = v_res_2017_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___boxed(lean_object* v_declName_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds(v_declName_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
return v_res_2026_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1(lean_object* v_cls_2027_, lean_object* v_msg_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(v_cls_2027_, v_msg_2028_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
return v___x_2036_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2027_ = stack[0].m_obj;
lean_object* v_msg_2028_ = stack[1].m_obj;
lean_object* v___y_2029_ = stack[2].m_obj;
lean_object* v___y_2030_ = stack[3].m_obj;
lean_object* v___y_2031_ = stack[4].m_obj;
lean_object* v___y_2032_ = stack[5].m_obj;
lean_object* v___y_2033_ = stack[6].m_obj;
lean_object* v___y_2034_ = stack[7].m_obj;
lean_object* v_res_2037_;
v_res_2037_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1(v_cls_2027_, v_msg_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
stack->m_obj
 = v_res_2037_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___boxed(lean_object* v_cls_2038_, lean_object* v_msg_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1(v_cls_2038_, v_msg_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2047_;
}
}
lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(lean_object* v_declName_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___x_2051_; lean_object* v_env_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2051_ = lean_st_ref_get(v___y_2049_);
v_env_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc_ref(v_env_2052_);
lean_dec(v___x_2051_);
v___x_2053_ = l_Lean_isInductiveCore(v_env_2052_, v_declName_2048_);
v___x_2054_ = lean_box(v___x_2053_);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2048_ = stack[0].m_obj;
lean_object* v___y_2049_ = stack[1].m_obj;
lean_object* v_res_2056_;
v_res_2056_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(v_declName_2048_, v___y_2049_);
stack->m_obj
 = v_res_2056_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg___boxed(lean_object* v_declName_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(v_declName_2057_, v___y_2058_);
lean_dec(v___y_2058_);
return v_res_2060_;
}
}
lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0(lean_object* v_declName_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(v_declName_2061_, v___y_2063_);
return v___x_2065_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2061_ = stack[0].m_obj;
lean_object* v___y_2062_ = stack[1].m_obj;
lean_object* v___y_2063_ = stack[2].m_obj;
lean_object* v_res_2066_;
v_res_2066_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0(v_declName_2061_, v___y_2062_, v___y_2063_);
stack->m_obj
 = v_res_2066_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___boxed(lean_object* v_declName_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0(v_declName_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2071_;
}
}
lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0(uint8_t v_____do__lift_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
if (v_____do__lift_2072_ == 0)
{
uint8_t v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = 1;
v___x_2077_ = lean_box(v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
else
{
uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = 0;
v___x_2080_ = lean_box(v___x_2079_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_2072_ = stack[0].m_num;
lean_object* v___y_2073_ = stack[1].m_obj;
lean_object* v___y_2074_ = stack[2].m_obj;
lean_object* v_res_2082_;
v_res_2082_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0(v_____do__lift_2072_, v___y_2073_, v___y_2074_);
stack->m_obj
 = v_res_2082_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0___boxed(lean_object* v_____do__lift_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
uint8_t v_____do__lift_3617__boxed_2087_; lean_object* v_res_2088_; 
v_____do__lift_3617__boxed_2087_ = lean_unbox(v_____do__lift_2083_);
v_res_2088_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0(v_____do__lift_3617__boxed_2087_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
return v_res_2088_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(lean_object* v_as_2089_, size_t v_i_2090_, size_t v_stop_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_usize_dec_eq(v_i_2090_, v_stop_2091_);
if (v___x_2099_ == 0)
{
uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = 1;
v___x_2101_ = lean_array_uget_borrowed(v_as_2089_, v_i_2090_);
lean_inc(v___x_2101_);
v___x_2102_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(v___x_2101_, v___y_2093_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2112_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2112_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2112_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
uint8_t v___x_2107_; 
v___x_2107_ = lean_unbox(v_a_2103_);
lean_dec(v_a_2103_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = lean_box(v___x_2100_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2108_);
v___x_2110_ = v___x_2105_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
else
{
lean_del_object(v___x_2105_);
goto v___jp_2095_;
}
}
}
else
{
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2122_; 
v_a_2113_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2115_ = v___x_2102_;
v_isShared_2116_ = v_isSharedCheck_2122_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2102_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2122_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
uint8_t v___x_2117_; 
v___x_2117_ = lean_unbox(v_a_2113_);
lean_dec(v_a_2113_);
if (v___x_2117_ == 0)
{
lean_del_object(v___x_2115_);
goto v___jp_2095_;
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2118_ = lean_box(v___x_2100_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set_tag(v___x_2115_, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2118_);
v___x_2120_ = v___x_2115_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
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
return v___x_2102_;
}
}
}
else
{
uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = 0;
v___x_2124_ = lean_box(v___x_2123_);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
v___jp_2095_:
{
size_t v___x_2096_; size_t v___x_2097_; 
v___x_2096_ = ((size_t)1ULL);
v___x_2097_ = lean_usize_add(v_i_2090_, v___x_2096_);
v_i_2090_ = v___x_2097_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2089_ = stack[0].m_obj;
size_t v_i_2090_ = stack[1].m_num;
size_t v_stop_2091_ = stack[2].m_num;
lean_object* v___y_2092_ = stack[3].m_obj;
lean_object* v___y_2093_ = stack[4].m_obj;
lean_object* v_res_2126_;
v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(v_as_2089_, v_i_2090_, v_stop_2091_, v___y_2092_, v___y_2093_);
stack->m_obj
 = v_res_2126_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3___boxed(lean_object* v_as_2127_, lean_object* v_i_2128_, lean_object* v_stop_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
size_t v_i_boxed_2133_; size_t v_stop_boxed_2134_; lean_object* v_res_2135_; 
v_i_boxed_2133_ = lean_unbox_usize(v_i_2128_);
lean_dec(v_i_2128_);
v_stop_boxed_2134_ = lean_unbox_usize(v_stop_2129_);
lean_dec(v_stop_2129_);
v_res_2135_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(v_as_2127_, v_i_boxed_2133_, v_stop_boxed_2134_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec_ref(v_as_2127_);
return v_res_2135_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(lean_object* v_as_2136_, size_t v_i_2137_, size_t v_stop_2138_, lean_object* v_b_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_usize_dec_eq(v_i_2137_, v_stop_2138_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_array_uget_borrowed(v_as_2136_, v_i_2137_);
lean_inc(v___x_2144_);
v___x_2145_ = l_Lean_Elab_Command_elabCommand(v___x_2144_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; size_t v___x_2147_; size_t v___x_2148_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2147_ = ((size_t)1ULL);
v___x_2148_ = lean_usize_add(v_i_2137_, v___x_2147_);
v_i_2137_ = v___x_2148_;
v_b_2139_ = v_a_2146_;
goto _start;
}
else
{
return v___x_2145_;
}
}
else
{
lean_object* v___x_2150_; 
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v_b_2139_);
return v___x_2150_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2136_ = stack[0].m_obj;
size_t v_i_2137_ = stack[1].m_num;
size_t v_stop_2138_ = stack[2].m_num;
lean_object* v_b_2139_ = stack[3].m_obj;
lean_object* v___y_2140_ = stack[4].m_obj;
lean_object* v___y_2141_ = stack[5].m_obj;
lean_object* v_res_2151_;
v_res_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_as_2136_, v_i_2137_, v_stop_2138_, v_b_2139_, v___y_2140_, v___y_2141_);
stack->m_obj
 = v_res_2151_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1___boxed(lean_object* v_as_2152_, lean_object* v_i_2153_, lean_object* v_stop_2154_, lean_object* v_b_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
size_t v_i_boxed_2159_; size_t v_stop_boxed_2160_; lean_object* v_res_2161_; 
v_i_boxed_2159_ = lean_unbox_usize(v_i_2153_);
lean_dec(v_i_2153_);
v_stop_boxed_2160_ = lean_unbox_usize(v_stop_2154_);
lean_dec(v_stop_2154_);
v_res_2161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_as_2152_, v_i_boxed_2159_, v_stop_boxed_2160_, v_b_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec_ref(v_as_2152_);
return v_res_2161_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0(lean_object* v___x_2162_, lean_object* v___x_2163_, lean_object* v___x_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_2162_, v___y_2165_, v___y_2166_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2188_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2188_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2188_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = lean_array_get_size(v_a_2169_);
v___x_2174_ = lean_nat_dec_lt(v___x_2163_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2176_; 
lean_dec(v_a_2169_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2164_);
v___x_2176_ = v___x_2171_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2164_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
else
{
uint8_t v___x_2178_; 
v___x_2178_ = lean_nat_dec_le(v___x_2173_, v___x_2173_);
if (v___x_2178_ == 0)
{
if (v___x_2174_ == 0)
{
lean_object* v___x_2180_; 
lean_dec(v_a_2169_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2164_);
v___x_2180_ = v___x_2171_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2164_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
else
{
size_t v___x_2182_; size_t v___x_2183_; lean_object* v___x_2184_; 
lean_del_object(v___x_2171_);
v___x_2182_ = ((size_t)0ULL);
v___x_2183_ = lean_usize_of_nat(v___x_2173_);
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_a_2169_, v___x_2182_, v___x_2183_, v___x_2164_, v___y_2165_, v___y_2166_);
lean_dec(v_a_2169_);
return v___x_2184_;
}
}
else
{
size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; 
lean_del_object(v___x_2171_);
v___x_2185_ = ((size_t)0ULL);
v___x_2186_ = lean_usize_of_nat(v___x_2173_);
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_a_2169_, v___x_2185_, v___x_2186_, v___x_2164_, v___y_2165_, v___y_2166_);
lean_dec(v_a_2169_);
return v___x_2187_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
v_a_2189_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2168_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2168_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2162_ = stack[0].m_obj;
lean_object* v___x_2163_ = stack[1].m_obj;
lean_object* v___x_2164_ = stack[2].m_obj;
lean_object* v___y_2165_ = stack[3].m_obj;
lean_object* v___y_2166_ = stack[4].m_obj;
lean_object* v_res_2197_;
v_res_2197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0(v___x_2162_, v___x_2163_, v___x_2164_, v___y_2165_, v___y_2166_);
stack->m_obj
 = v_res_2197_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0___boxed(lean_object* v___x_2198_, lean_object* v___x_2199_, lean_object* v___x_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0(v___x_2198_, v___x_2199_, v___x_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___x_2199_);
return v_res_2204_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(lean_object* v_as_2205_, size_t v_sz_2206_, size_t v_i_2207_, lean_object* v_b_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
uint8_t v___x_2212_; 
v___x_2212_ = lean_usize_dec_lt(v_i_2207_, v_sz_2206_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; 
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_b_2208_);
return v___x_2213_;
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v_a_2216_; lean_object* v___x_2217_; lean_object* v___f_2218_; lean_object* v___x_2219_; 
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = lean_box(0);
v_a_2216_ = lean_array_uget_borrowed(v_as_2205_, v_i_2207_);
lean_inc_n(v_a_2216_, 2);
v___x_2217_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_2217_, 0, v_a_2216_);
v___f_2218_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2218_, 0, v___x_2217_);
lean_closure_set(v___f_2218_, 1, v___x_2214_);
lean_closure_set(v___f_2218_, 2, v___x_2215_);
v___x_2219_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_2216_, v___f_2218_, v___y_2209_, v___y_2210_);
if (lean_obj_tag(v___x_2219_) == 0)
{
size_t v___x_2220_; size_t v___x_2221_; 
lean_dec_ref_known(v___x_2219_, 1);
v___x_2220_ = ((size_t)1ULL);
v___x_2221_ = lean_usize_add(v_i_2207_, v___x_2220_);
v_i_2207_ = v___x_2221_;
v_b_2208_ = v___x_2215_;
goto _start;
}
else
{
return v___x_2219_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2205_ = stack[0].m_obj;
size_t v_sz_2206_ = stack[1].m_num;
size_t v_i_2207_ = stack[2].m_num;
lean_object* v_b_2208_ = stack[3].m_obj;
lean_object* v___y_2209_ = stack[4].m_obj;
lean_object* v___y_2210_ = stack[5].m_obj;
lean_object* v_res_2223_;
v_res_2223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(v_as_2205_, v_sz_2206_, v_i_2207_, v_b_2208_, v___y_2209_, v___y_2210_);
stack->m_obj
 = v_res_2223_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___boxed(lean_object* v_as_2224_, lean_object* v_sz_2225_, lean_object* v_i_2226_, lean_object* v_b_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
size_t v_sz_boxed_2231_; size_t v_i_boxed_2232_; lean_object* v_res_2233_; 
v_sz_boxed_2231_ = lean_unbox_usize(v_sz_2225_);
lean_dec(v_sz_2225_);
v_i_boxed_2232_ = lean_unbox_usize(v_i_2226_);
lean_dec(v_i_2226_);
v_res_2233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(v_as_2224_, v_sz_boxed_2231_, v_i_boxed_2232_, v_b_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_as_2224_);
return v_res_2233_;
}
}
lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1(lean_object* v_declNames_2234_, lean_object* v___x_2235_, lean_object* v___x_2236_, lean_object* v___f_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___y_2265_; uint8_t v___x_2268_; 
v___x_2268_ = lean_nat_dec_lt(v___x_2235_, v___x_2236_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_box(v___x_2268_);
lean_inc(v___y_2239_);
lean_inc_ref(v___y_2238_);
v___x_2270_ = lean_apply_4(v___f_2237_, v___x_2269_, v___y_2238_, v___y_2239_, lean_box(0));
v___y_2265_ = v___x_2270_;
goto v___jp_2264_;
}
else
{
if (v___x_2268_ == 0)
{
lean_dec_ref(v___f_2237_);
goto v___jp_2241_;
}
else
{
size_t v___x_2271_; size_t v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = lean_usize_of_nat(v___x_2236_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(v_declNames_2234_, v___x_2271_, v___x_2272_, v___y_2238_, v___y_2239_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2273_, 1);
lean_inc(v___y_2239_);
lean_inc_ref(v___y_2238_);
v___x_2275_ = lean_apply_4(v___f_2237_, v_a_2274_, v___y_2238_, v___y_2239_, lean_box(0));
v___y_2265_ = v___x_2275_;
goto v___jp_2264_;
}
else
{
lean_dec_ref(v___f_2237_);
v___y_2265_ = v___x_2273_;
goto v___jp_2264_;
}
}
}
v___jp_2241_:
{
uint8_t v___x_2242_; lean_object* v___x_2243_; size_t v_sz_2244_; size_t v___x_2245_; lean_object* v___x_2246_; 
v___x_2242_ = 1;
v___x_2243_ = lean_box(0);
v_sz_2244_ = lean_array_size(v_declNames_2234_);
v___x_2245_ = ((size_t)0ULL);
v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(v_declNames_2234_, v_sz_2244_, v___x_2245_, v___x_2243_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2254_; 
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; 
v_unused_2255_ = lean_ctor_get(v___x_2246_, 0);
lean_dec(v_unused_2255_);
v___x_2248_ = v___x_2246_;
v_isShared_2249_ = v_isSharedCheck_2254_;
goto v_resetjp_2247_;
}
else
{
lean_dec(v___x_2246_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2254_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_box(v___x_2242_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2250_);
v___x_2252_ = v___x_2248_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
v_a_2256_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2246_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2246_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
v___jp_2264_:
{
if (lean_obj_tag(v___y_2265_) == 0)
{
lean_object* v_a_2266_; uint8_t v___x_2267_; 
v_a_2266_ = lean_ctor_get(v___y_2265_, 0);
v___x_2267_ = lean_unbox(v_a_2266_);
if (v___x_2267_ == 0)
{
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
return v___y_2265_;
}
else
{
lean_dec_ref_known(v___y_2265_, 1);
goto v___jp_2241_;
}
}
else
{
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
return v___y_2265_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_2234_ = stack[0].m_obj;
lean_object* v___x_2235_ = stack[1].m_obj;
lean_object* v___x_2236_ = stack[2].m_obj;
lean_object* v___f_2237_ = stack[3].m_obj;
lean_object* v___y_2238_ = stack[4].m_obj;
lean_object* v___y_2239_ = stack[5].m_obj;
lean_object* v_res_2276_;
v_res_2276_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1(v_declNames_2234_, v___x_2235_, v___x_2236_, v___f_2237_, v___y_2238_, v___y_2239_);
stack->m_obj
 = v_res_2276_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1___boxed(lean_object* v_declNames_2277_, lean_object* v___x_2278_, lean_object* v___x_2279_, lean_object* v___f_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1(v_declNames_2277_, v___x_2278_, v___x_2279_, v___f_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v_declNames_2277_);
return v_res_2284_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(lean_object* v___y_2285_, uint8_t v_isExporting_2286_, lean_object* v_a_x3f_2287_){
_start:
{
lean_object* v___x_2289_; lean_object* v_env_2290_; lean_object* v_messages_2291_; lean_object* v_scopes_2292_; lean_object* v_usedQuotCtxts_2293_; lean_object* v_nextMacroScope_2294_; lean_object* v_maxRecDepth_2295_; lean_object* v_ngen_2296_; lean_object* v_auxDeclNGen_2297_; lean_object* v_infoState_2298_; lean_object* v_traceState_2299_; lean_object* v_snapshotTasks_2300_; lean_object* v_prevLinterStates_2301_; lean_object* v_codeQualityEntryTasks_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2313_; 
v___x_2289_ = lean_st_ref_take(v___y_2285_);
v_env_2290_ = lean_ctor_get(v___x_2289_, 0);
v_messages_2291_ = lean_ctor_get(v___x_2289_, 1);
v_scopes_2292_ = lean_ctor_get(v___x_2289_, 2);
v_usedQuotCtxts_2293_ = lean_ctor_get(v___x_2289_, 3);
v_nextMacroScope_2294_ = lean_ctor_get(v___x_2289_, 4);
v_maxRecDepth_2295_ = lean_ctor_get(v___x_2289_, 5);
v_ngen_2296_ = lean_ctor_get(v___x_2289_, 6);
v_auxDeclNGen_2297_ = lean_ctor_get(v___x_2289_, 7);
v_infoState_2298_ = lean_ctor_get(v___x_2289_, 8);
v_traceState_2299_ = lean_ctor_get(v___x_2289_, 9);
v_snapshotTasks_2300_ = lean_ctor_get(v___x_2289_, 10);
v_prevLinterStates_2301_ = lean_ctor_get(v___x_2289_, 11);
v_codeQualityEntryTasks_2302_ = lean_ctor_get(v___x_2289_, 12);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2304_ = v___x_2289_;
v_isShared_2305_ = v_isSharedCheck_2313_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2302_);
lean_inc(v_prevLinterStates_2301_);
lean_inc(v_snapshotTasks_2300_);
lean_inc(v_traceState_2299_);
lean_inc(v_infoState_2298_);
lean_inc(v_auxDeclNGen_2297_);
lean_inc(v_ngen_2296_);
lean_inc(v_maxRecDepth_2295_);
lean_inc(v_nextMacroScope_2294_);
lean_inc(v_usedQuotCtxts_2293_);
lean_inc(v_scopes_2292_);
lean_inc(v_messages_2291_);
lean_inc(v_env_2290_);
lean_dec(v___x_2289_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2313_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2306_ = lean_box(0);
v___x_2307_ = l_Lean_Environment_setExporting(v_env_2290_, v_isExporting_2286_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2307_);
v___x_2309_ = v___x_2304_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_messages_2291_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_scopes_2292_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v_usedQuotCtxts_2293_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v_nextMacroScope_2294_);
lean_ctor_set(v_reuseFailAlloc_2312_, 5, v_maxRecDepth_2295_);
lean_ctor_set(v_reuseFailAlloc_2312_, 6, v_ngen_2296_);
lean_ctor_set(v_reuseFailAlloc_2312_, 7, v_auxDeclNGen_2297_);
lean_ctor_set(v_reuseFailAlloc_2312_, 8, v_infoState_2298_);
lean_ctor_set(v_reuseFailAlloc_2312_, 9, v_traceState_2299_);
lean_ctor_set(v_reuseFailAlloc_2312_, 10, v_snapshotTasks_2300_);
lean_ctor_set(v_reuseFailAlloc_2312_, 11, v_prevLinterStates_2301_);
lean_ctor_set(v_reuseFailAlloc_2312_, 12, v_codeQualityEntryTasks_2302_);
v___x_2309_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_st_ref_put(v___y_2285_, v___x_2309_);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2306_);
return v___x_2311_;
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2285_ = stack[0].m_obj;
uint8_t v_isExporting_2286_ = stack[1].m_num;
lean_object* v_a_x3f_2287_ = stack[2].m_obj;
lean_object* v_res_2314_;
v_res_2314_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_2285_, v_isExporting_2286_, v_a_x3f_2287_);
stack->m_obj
 = v_res_2314_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v___y_2315_, lean_object* v_isExporting_2316_, lean_object* v_a_x3f_2317_, lean_object* v___y_2318_){
_start:
{
uint8_t v_isExporting_boxed_2319_; lean_object* v_res_2320_; 
v_isExporting_boxed_2319_ = lean_unbox(v_isExporting_2316_);
v_res_2320_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_2315_, v_isExporting_boxed_2319_, v_a_x3f_2317_);
lean_dec(v_a_x3f_2317_);
lean_dec(v___y_2315_);
return v_res_2320_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(lean_object* v_x_2321_, uint8_t v_isExporting_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v___x_2326_; lean_object* v_env_2327_; lean_object* v___x_2328_; uint8_t v_isModule_2329_; 
v___x_2326_ = lean_st_ref_get(v___y_2324_);
v_env_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc_ref(v_env_2327_);
lean_dec(v___x_2326_);
v___x_2328_ = l_Lean_Environment_header(v_env_2327_);
v_isModule_2329_ = lean_ctor_get_uint8(v___x_2328_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2328_);
if (v_isModule_2329_ == 0)
{
lean_object* v___x_2330_; 
lean_dec_ref(v_env_2327_);
lean_inc(v___y_2324_);
lean_inc_ref(v___y_2323_);
v___x_2330_ = lean_apply_3(v_x_2321_, v___y_2323_, v___y_2324_, lean_box(0));
return v___x_2330_;
}
else
{
uint8_t v_isExporting_2331_; 
v_isExporting_2331_ = lean_ctor_get_uint8(v_env_2327_, sizeof(void*)*13);
lean_dec_ref(v_env_2327_);
if (v_isExporting_2322_ == 0)
{
if (v_isExporting_2331_ == 0)
{
lean_object* v___x_2385_; 
lean_inc(v___y_2324_);
lean_inc_ref(v___y_2323_);
v___x_2385_ = lean_apply_3(v_x_2321_, v___y_2323_, v___y_2324_, lean_box(0));
return v___x_2385_;
}
else
{
goto v___jp_2332_;
}
}
else
{
if (v_isExporting_2331_ == 0)
{
goto v___jp_2332_;
}
else
{
lean_object* v___x_2386_; 
lean_inc(v___y_2324_);
lean_inc_ref(v___y_2323_);
v___x_2386_ = lean_apply_3(v_x_2321_, v___y_2323_, v___y_2324_, lean_box(0));
return v___x_2386_;
}
}
v___jp_2332_:
{
lean_object* v___x_2333_; lean_object* v_env_2334_; lean_object* v_messages_2335_; lean_object* v_scopes_2336_; lean_object* v_usedQuotCtxts_2337_; lean_object* v_nextMacroScope_2338_; lean_object* v_maxRecDepth_2339_; lean_object* v_ngen_2340_; lean_object* v_auxDeclNGen_2341_; lean_object* v_infoState_2342_; lean_object* v_traceState_2343_; lean_object* v_snapshotTasks_2344_; lean_object* v_prevLinterStates_2345_; lean_object* v_codeQualityEntryTasks_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2384_; 
v___x_2333_ = lean_st_ref_take(v___y_2324_);
v_env_2334_ = lean_ctor_get(v___x_2333_, 0);
v_messages_2335_ = lean_ctor_get(v___x_2333_, 1);
v_scopes_2336_ = lean_ctor_get(v___x_2333_, 2);
v_usedQuotCtxts_2337_ = lean_ctor_get(v___x_2333_, 3);
v_nextMacroScope_2338_ = lean_ctor_get(v___x_2333_, 4);
v_maxRecDepth_2339_ = lean_ctor_get(v___x_2333_, 5);
v_ngen_2340_ = lean_ctor_get(v___x_2333_, 6);
v_auxDeclNGen_2341_ = lean_ctor_get(v___x_2333_, 7);
v_infoState_2342_ = lean_ctor_get(v___x_2333_, 8);
v_traceState_2343_ = lean_ctor_get(v___x_2333_, 9);
v_snapshotTasks_2344_ = lean_ctor_get(v___x_2333_, 10);
v_prevLinterStates_2345_ = lean_ctor_get(v___x_2333_, 11);
v_codeQualityEntryTasks_2346_ = lean_ctor_get(v___x_2333_, 12);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2348_ = v___x_2333_;
v_isShared_2349_ = v_isSharedCheck_2384_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2346_);
lean_inc(v_prevLinterStates_2345_);
lean_inc(v_snapshotTasks_2344_);
lean_inc(v_traceState_2343_);
lean_inc(v_infoState_2342_);
lean_inc(v_auxDeclNGen_2341_);
lean_inc(v_ngen_2340_);
lean_inc(v_maxRecDepth_2339_);
lean_inc(v_nextMacroScope_2338_);
lean_inc(v_usedQuotCtxts_2337_);
lean_inc(v_scopes_2336_);
lean_inc(v_messages_2335_);
lean_inc(v_env_2334_);
lean_dec(v___x_2333_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2384_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2350_ = l_Lean_Environment_setExporting(v_env_2334_, v_isExporting_2322_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2350_);
v___x_2352_ = v___x_2348_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_messages_2335_);
lean_ctor_set(v_reuseFailAlloc_2383_, 2, v_scopes_2336_);
lean_ctor_set(v_reuseFailAlloc_2383_, 3, v_usedQuotCtxts_2337_);
lean_ctor_set(v_reuseFailAlloc_2383_, 4, v_nextMacroScope_2338_);
lean_ctor_set(v_reuseFailAlloc_2383_, 5, v_maxRecDepth_2339_);
lean_ctor_set(v_reuseFailAlloc_2383_, 6, v_ngen_2340_);
lean_ctor_set(v_reuseFailAlloc_2383_, 7, v_auxDeclNGen_2341_);
lean_ctor_set(v_reuseFailAlloc_2383_, 8, v_infoState_2342_);
lean_ctor_set(v_reuseFailAlloc_2383_, 9, v_traceState_2343_);
lean_ctor_set(v_reuseFailAlloc_2383_, 10, v_snapshotTasks_2344_);
lean_ctor_set(v_reuseFailAlloc_2383_, 11, v_prevLinterStates_2345_);
lean_ctor_set(v_reuseFailAlloc_2383_, 12, v_codeQualityEntryTasks_2346_);
v___x_2352_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2353_; lean_object* v_r_2354_; 
v___x_2353_ = lean_st_ref_put(v___y_2324_, v___x_2352_);
lean_inc(v___y_2324_);
lean_inc_ref(v___y_2323_);
v_r_2354_ = lean_apply_3(v_x_2321_, v___y_2323_, v___y_2324_, lean_box(0));
if (lean_obj_tag(v_r_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2371_; 
v_a_2355_ = lean_ctor_get(v_r_2354_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_r_2354_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2357_ = v_r_2354_;
v_isShared_2358_ = v_isSharedCheck_2371_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v_r_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2371_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
lean_inc(v_a_2355_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set_tag(v___x_2357_, 1);
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v___x_2361_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_2324_, v_isExporting_2331_, v___x_2360_);
lean_dec_ref(v___x_2360_);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; 
v_unused_2369_ = lean_ctor_get(v___x_2361_, 0);
lean_dec(v_unused_2369_);
v___x_2363_ = v___x_2361_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_dec(v___x_2361_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v_a_2355_);
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2355_);
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
else
{
lean_object* v_a_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
v_a_2372_ = lean_ctor_get(v_r_2354_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v_r_2354_, 1);
v___x_2373_ = lean_box(0);
v___x_2374_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_2324_, v_isExporting_2331_, v___x_2373_);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; 
v_unused_2382_ = lean_ctor_get(v___x_2374_, 0);
lean_dec(v_unused_2382_);
v___x_2376_ = v___x_2374_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_dec(v___x_2374_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
lean_ctor_set_tag(v___x_2376_, 1);
lean_ctor_set(v___x_2376_, 0, v_a_2372_);
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2372_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2321_ = stack[0].m_obj;
uint8_t v_isExporting_2322_ = stack[1].m_num;
lean_object* v___y_2323_ = stack[2].m_obj;
lean_object* v___y_2324_ = stack[3].m_obj;
lean_object* v_res_2387_;
v_res_2387_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_2321_, v_isExporting_2322_, v___y_2323_, v___y_2324_);
stack->m_obj
 = v_res_2387_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___boxed(lean_object* v_x_2388_, lean_object* v_isExporting_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
uint8_t v_isExporting_boxed_2393_; lean_object* v_res_2394_; 
v_isExporting_boxed_2393_ = lean_unbox(v_isExporting_2389_);
v_res_2394_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_2388_, v_isExporting_boxed_2393_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
return v_res_2394_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(lean_object* v_x_2395_, uint8_t v_when_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
if (v_when_2396_ == 0)
{
lean_object* v___x_2400_; 
lean_inc(v___y_2398_);
lean_inc_ref(v___y_2397_);
v___x_2400_ = lean_apply_3(v_x_2395_, v___y_2397_, v___y_2398_, lean_box(0));
return v___x_2400_;
}
else
{
uint8_t v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = 0;
v___x_2402_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_2395_, v___x_2401_, v___y_2397_, v___y_2398_);
return v___x_2402_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2395_ = stack[0].m_obj;
uint8_t v_when_2396_ = stack[1].m_num;
lean_object* v___y_2397_ = stack[2].m_obj;
lean_object* v___y_2398_ = stack[3].m_obj;
lean_object* v_res_2403_;
v_res_2403_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v_x_2395_, v_when_2396_, v___y_2397_, v___y_2398_);
stack->m_obj
 = v_res_2403_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg___boxed(lean_object* v_x_2404_, lean_object* v_when_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
uint8_t v_when_boxed_2409_; lean_object* v_res_2410_; 
v_when_boxed_2409_ = lean_unbox(v_when_2405_);
v_res_2410_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v_x_2404_, v_when_boxed_2409_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2410_;
}
}
lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler(lean_object* v_declNames_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v___f_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___f_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; 
v___f_2416_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHandler___closed__0));
v___x_2417_ = lean_unsigned_to_nat(0u);
v___x_2418_ = lean_array_get_size(v_declNames_2412_);
v___f_2419_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1___boxed), 7, 4);
lean_closure_set(v___f_2419_, 0, v_declNames_2412_);
lean_closure_set(v___f_2419_, 1, v___x_2417_);
lean_closure_set(v___f_2419_, 2, v___x_2418_);
lean_closure_set(v___f_2419_, 3, v___f_2416_);
v___x_2420_ = 1;
v___x_2421_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v___f_2419_, v___x_2420_, v_a_2413_, v_a_2414_);
return v___x_2421_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Hashable_mkHashableHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_2412_ = stack[0].m_obj;
lean_object* v_a_2413_ = stack[1].m_obj;
lean_object* v_a_2414_ = stack[2].m_obj;
lean_object* v_res_2422_;
v_res_2422_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler(v_declNames_2412_, v_a_2413_, v_a_2414_);
stack->m_obj
 = v_res_2422_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___boxed(lean_object* v_declNames_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler(v_declNames_2423_, v_a_2424_, v_a_2425_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
return v_res_2427_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4(lean_object* v_00_u03b1_2428_, lean_object* v_x_2429_, uint8_t v_isExporting_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_2429_, v_isExporting_2430_, v___y_2431_, v___y_2432_);
return v___x_2434_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2429_ = stack[1].m_obj;
uint8_t v_isExporting_2430_ = stack[2].m_num;
lean_object* v___y_2431_ = stack[3].m_obj;
lean_object* v___y_2432_ = stack[4].m_obj;
lean_object* v_res_2435_;
v_res_2435_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4(lean_box(0), v_x_2429_, v_isExporting_2430_, v___y_2431_, v___y_2432_);
stack->m_obj
 = v_res_2435_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2436_, lean_object* v_x_2437_, lean_object* v_isExporting_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
uint8_t v_isExporting_boxed_2442_; lean_object* v_res_2443_; 
v_isExporting_boxed_2442_ = lean_unbox(v_isExporting_2438_);
v_res_2443_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4(v_00_u03b1_2436_, v_x_2437_, v_isExporting_boxed_2442_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2443_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4(lean_object* v_00_u03b1_2444_, lean_object* v_x_2445_, uint8_t v_when_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v_x_2445_, v_when_2446_, v___y_2447_, v___y_2448_);
return v___x_2450_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2445_ = stack[1].m_obj;
uint8_t v_when_2446_ = stack[2].m_num;
lean_object* v___y_2447_ = stack[3].m_obj;
lean_object* v___y_2448_ = stack[4].m_obj;
lean_object* v_res_2451_;
v_res_2451_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4(lean_box(0), v_x_2445_, v_when_2446_, v___y_2447_, v___y_2448_);
stack->m_obj
 = v_res_2451_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___boxed(lean_object* v_00_u03b1_2452_, lean_object* v_x_2453_, lean_object* v_when_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
uint8_t v_when_boxed_2458_; lean_object* v_res_2459_; 
v_when_boxed_2458_ = lean_unbox(v_when_2454_);
v_res_2459_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4(v_00_u03b1_2452_, v_x_2453_, v_when_boxed_2458_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
return v_res_2459_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = lean_unsigned_to_nat(4079464183u);
v___x_2513_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__19_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2514_ = l_Lean_Name_num___override(v___x_2513_, v___x_2512_);
return v___x_2514_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__21_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2517_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2518_ = l_Lean_Name_str___override(v___x_2517_, v___x_2516_);
return v___x_2518_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__23_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2521_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2522_ = l_Lean_Name_str___override(v___x_2521_, v___x_2520_);
return v___x_2522_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = lean_unsigned_to_nat(2u);
v___x_2524_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2525_ = l_Lean_Name_num___override(v___x_2524_, v___x_2523_);
return v___x_2525_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1));
v___x_2528_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__0_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2529_ = l_Lean_Elab_registerDerivingHandler(v___x_2527_, v___x_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v___x_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_dec_ref_known(v___x_2529_, 1);
v___x_2530_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1));
v___x_2531_ = 0;
v___x_2532_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2533_ = l_Lean_registerTraceClass(v___x_2530_, v___x_2531_, v___x_2532_);
return v___x_2533_;
}
else
{
return v___x_2529_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2534_;
v_res_2534_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2534_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2____boxed(lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_();
return v_res_2536_;
}
}
lean_object* runtime_initialize_Lean_Meta_Inductive(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Inductive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Inductive(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Inductive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_Hashable(builtin);
}
#ifdef __cplusplus
}
#endif
