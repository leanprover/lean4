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
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
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
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
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
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHeader(lean_object* v_indVal_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1));
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = l_Lean_Elab_Deriving_mkHeader(v___x_12_, v___x_13_, v_indVal_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHeader___boxed(lean_object* v_indVal_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader(v_indVal_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
lean_dec(v_a_19_);
lean_dec_ref(v_a_18_);
lean_dec(v_a_17_);
lean_dec_ref(v_a_16_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0(lean_object* v_k_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v_b_27_, lean_object* v_c_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; 
lean_inc(v___y_32_);
lean_inc_ref(v___y_31_);
lean_inc(v___y_30_);
lean_inc_ref(v___y_29_);
lean_inc(v___y_26_);
lean_inc_ref(v___y_25_);
v___x_34_ = lean_apply_9(v_k_24_, v_b_27_, v_c_28_, v___y_25_, v___y_26_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, lean_box(0));
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0___boxed(lean_object* v_k_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v_b_38_, lean_object* v_c_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0(v_k_35_, v___y_36_, v___y_37_, v_b_38_, v_c_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(lean_object* v_type_46_, lean_object* v_k_47_, uint8_t v_cleanupAnnotations_48_, uint8_t v_whnfType_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___f_57_; lean_object* v___x_58_; 
lean_inc(v___y_51_);
lean_inc_ref(v___y_50_);
v___f_57_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_57_, 0, v_k_47_);
lean_closure_set(v___f_57_, 1, v___y_50_);
lean_closure_set(v___f_57_, 2, v___y_51_);
v___x_58_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_46_, v___f_57_, v_cleanupAnnotations_48_, v_whnfType_49_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_58_) == 0)
{
return v___x_58_;
}
else
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
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___boxed(lean_object* v_type_67_, lean_object* v_k_68_, lean_object* v_cleanupAnnotations_69_, lean_object* v_whnfType_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_78_; uint8_t v_whnfType_boxed_79_; lean_object* v_res_80_; 
v_cleanupAnnotations_boxed_78_ = lean_unbox(v_cleanupAnnotations_69_);
v_whnfType_boxed_79_ = lean_unbox(v_whnfType_70_);
v_res_80_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_type_67_, v_k_68_, v_cleanupAnnotations_boxed_78_, v_whnfType_boxed_79_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5(lean_object* v_00_u03b1_81_, lean_object* v_type_82_, lean_object* v_k_83_, uint8_t v_cleanupAnnotations_84_, uint8_t v_whnfType_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_type_82_, v_k_83_, v_cleanupAnnotations_84_, v_whnfType_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___boxed(lean_object* v_00_u03b1_94_, lean_object* v_type_95_, lean_object* v_k_96_, lean_object* v_cleanupAnnotations_97_, lean_object* v_whnfType_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_106_; uint8_t v_whnfType_boxed_107_; lean_object* v_res_108_; 
v_cleanupAnnotations_boxed_106_ = lean_unbox(v_cleanupAnnotations_97_);
v_whnfType_boxed_107_ = lean_unbox(v_whnfType_98_);
v_res_108_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5(v_00_u03b1_94_, v_type_95_, v_k_96_, v_cleanupAnnotations_boxed_106_, v_whnfType_boxed_107_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_108_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_instMonadEIO(lean_box(0));
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(lean_object* v_msg_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v_toApplicative_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_217_; 
v___x_124_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0);
v___x_125_ = l_StateRefT_x27_instMonad___redArg(v___x_124_);
v_toApplicative_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v___x_125_, 1);
lean_dec(v_unused_218_);
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_217_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_toApplicative_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_217_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v_toFunctor_130_; lean_object* v_toSeq_131_; lean_object* v_toSeqLeft_132_; lean_object* v_toSeqRight_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_215_; 
v_toFunctor_130_ = lean_ctor_get(v_toApplicative_126_, 0);
v_toSeq_131_ = lean_ctor_get(v_toApplicative_126_, 2);
v_toSeqLeft_132_ = lean_ctor_get(v_toApplicative_126_, 3);
v_toSeqRight_133_ = lean_ctor_get(v_toApplicative_126_, 4);
v_isSharedCheck_215_ = !lean_is_exclusive(v_toApplicative_126_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v_toApplicative_126_, 1);
lean_dec(v_unused_216_);
v___x_135_ = v_toApplicative_126_;
v_isShared_136_ = v_isSharedCheck_215_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_toSeqRight_133_);
lean_inc(v_toSeqLeft_132_);
lean_inc(v_toSeq_131_);
lean_inc(v_toFunctor_130_);
lean_dec(v_toApplicative_126_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_215_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___x_146_; 
v___f_137_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__1));
v___f_138_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_130_);
v___f_139_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_139_, 0, v_toFunctor_130_);
v___f_140_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_140_, 0, v_toFunctor_130_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___f_139_);
lean_ctor_set(v___x_141_, 1, v___f_140_);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_142_, 0, v_toSeqRight_133_);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_143_, 0, v_toSeqLeft_132_);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_144_, 0, v_toSeq_131_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 4, v___f_142_);
lean_ctor_set(v___x_135_, 3, v___f_143_);
lean_ctor_set(v___x_135_, 2, v___f_144_);
lean_ctor_set(v___x_135_, 1, v___f_137_);
lean_ctor_set(v___x_135_, 0, v___x_141_);
v___x_146_ = v___x_135_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___f_137_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v___f_144_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v___f_143_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v___f_142_);
v___x_146_ = v_reuseFailAlloc_214_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_148_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v___f_138_);
lean_ctor_set(v___x_128_, 0, v___x_146_);
v___x_148_ = v___x_128_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___f_138_);
v___x_148_ = v_reuseFailAlloc_213_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; lean_object* v_toApplicative_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_211_; 
v___x_149_ = l_StateRefT_x27_instMonad___redArg(v___x_148_);
v_toApplicative_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v___x_149_, 1);
lean_dec(v_unused_212_);
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_211_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_toApplicative_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_211_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_toFunctor_154_; lean_object* v_toSeq_155_; lean_object* v_toSeqLeft_156_; lean_object* v_toSeqRight_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_209_; 
v_toFunctor_154_ = lean_ctor_get(v_toApplicative_150_, 0);
v_toSeq_155_ = lean_ctor_get(v_toApplicative_150_, 2);
v_toSeqLeft_156_ = lean_ctor_get(v_toApplicative_150_, 3);
v_toSeqRight_157_ = lean_ctor_get(v_toApplicative_150_, 4);
v_isSharedCheck_209_ = !lean_is_exclusive(v_toApplicative_150_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v_toApplicative_150_, 1);
lean_dec(v_unused_210_);
v___x_159_ = v_toApplicative_150_;
v_isShared_160_ = v_isSharedCheck_209_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_toSeqRight_157_);
lean_inc(v_toSeqLeft_156_);
lean_inc(v_toSeq_155_);
lean_inc(v_toFunctor_154_);
lean_dec(v_toApplicative_150_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_209_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_170_; 
v___f_161_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__3));
v___f_162_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_154_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_163_, 0, v_toFunctor_154_);
v___f_164_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_164_, 0, v_toFunctor_154_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___f_163_);
lean_ctor_set(v___x_165_, 1, v___f_164_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_166_, 0, v_toSeqRight_157_);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_167_, 0, v_toSeqLeft_156_);
v___f_168_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_168_, 0, v_toSeq_155_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 4, v___f_166_);
lean_ctor_set(v___x_159_, 3, v___f_167_);
lean_ctor_set(v___x_159_, 2, v___f_168_);
lean_ctor_set(v___x_159_, 1, v___f_161_);
lean_ctor_set(v___x_159_, 0, v___x_165_);
v___x_170_ = v___x_159_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___f_161_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v___f_168_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v___f_167_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v___f_166_);
v___x_170_ = v_reuseFailAlloc_208_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___f_162_);
lean_ctor_set(v___x_152_, 0, v___x_170_);
v___x_172_ = v___x_152_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v___f_162_);
v___x_172_ = v_reuseFailAlloc_207_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v_toApplicative_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_205_; 
v___x_173_ = l_StateRefT_x27_instMonad___redArg(v___x_172_);
v_toApplicative_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v___x_173_, 1);
lean_dec(v_unused_206_);
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_205_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_toApplicative_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_205_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_toFunctor_178_; lean_object* v_toSeq_179_; lean_object* v_toSeqLeft_180_; lean_object* v_toSeqRight_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_203_; 
v_toFunctor_178_ = lean_ctor_get(v_toApplicative_174_, 0);
v_toSeq_179_ = lean_ctor_get(v_toApplicative_174_, 2);
v_toSeqLeft_180_ = lean_ctor_get(v_toApplicative_174_, 3);
v_toSeqRight_181_ = lean_ctor_get(v_toApplicative_174_, 4);
v_isSharedCheck_203_ = !lean_is_exclusive(v_toApplicative_174_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v_toApplicative_174_, 1);
lean_dec(v_unused_204_);
v___x_183_ = v_toApplicative_174_;
v_isShared_184_ = v_isSharedCheck_203_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_toSeqRight_181_);
lean_inc(v_toSeqLeft_180_);
lean_inc(v_toSeq_179_);
lean_inc(v_toFunctor_178_);
lean_dec(v_toApplicative_174_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_203_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___x_194_; 
v___f_185_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__5));
v___f_186_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_178_);
v___f_187_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_187_, 0, v_toFunctor_178_);
v___f_188_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_188_, 0, v_toFunctor_178_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___f_187_);
lean_ctor_set(v___x_189_, 1, v___f_188_);
v___f_190_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_190_, 0, v_toSeqRight_181_);
v___f_191_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_191_, 0, v_toSeqLeft_180_);
v___f_192_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_192_, 0, v_toSeq_179_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 4, v___f_190_);
lean_ctor_set(v___x_183_, 3, v___f_191_);
lean_ctor_set(v___x_183_, 2, v___f_192_);
lean_ctor_set(v___x_183_, 1, v___f_185_);
lean_ctor_set(v___x_183_, 0, v___x_189_);
v___x_194_ = v___x_183_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___f_185_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v___f_192_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v___f_191_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v___f_190_);
v___x_194_ = v_reuseFailAlloc_202_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_196_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v___f_186_);
lean_ctor_set(v___x_176_, 0, v___x_194_);
v___x_196_ = v___x_176_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___f_186_);
v___x_196_ = v_reuseFailAlloc_201_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_30518__overap_199_; lean_object* v___x_200_; 
v___x_197_ = lean_box(0);
v___x_198_ = l_instInhabitedOfMonad___redArg(v___x_196_, v___x_197_);
v___x_30518__overap_199_ = lean_panic_fn_borrowed(v___x_198_, v_msg_116_);
lean_dec(v___x_198_);
lean_inc(v___y_122_);
lean_inc_ref(v___y_121_);
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
lean_inc(v___y_118_);
lean_inc_ref(v___y_117_);
v___x_200_ = lean_apply_7(v___x_30518__overap_199_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, lean_box(0));
return v___x_200_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(v_msg_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v_env_235_; lean_object* v___x_236_; lean_object* v_toCold_237_; lean_object* v_mctx_238_; lean_object* v_lctx_239_; lean_object* v_options_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_234_ = lean_st_ref_get(v___y_232_);
v_env_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc_ref(v_env_235_);
lean_dec(v___x_234_);
v___x_236_ = lean_st_ref_get(v___y_230_);
v_toCold_237_ = lean_ctor_get(v___y_231_, 0);
v_mctx_238_ = lean_ctor_get(v___x_236_, 0);
lean_inc_ref(v_mctx_238_);
lean_dec(v___x_236_);
v_lctx_239_ = lean_ctor_get(v___y_229_, 2);
v_options_240_ = lean_ctor_get(v_toCold_237_, 2);
lean_inc_ref(v_options_240_);
lean_inc_ref(v_lctx_239_);
v___x_241_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_241_, 0, v_env_235_);
lean_ctor_set(v___x_241_, 1, v_mctx_238_);
lean_ctor_set(v___x_241_, 2, v_lctx_239_);
lean_ctor_set(v___x_241_, 3, v_options_240_);
v___x_242_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v_msgData_228_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msgData_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
return v_res_250_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_box(1);
v___x_252_ = l_Lean_MessageData_ofFormat(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2));
v___x_257_ = l_Lean_MessageData_ofFormat(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12(lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
return v_x_258_;
}
else
{
lean_object* v_head_260_; lean_object* v_tail_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_283_; 
v_head_260_ = lean_ctor_get(v_x_259_, 0);
v_tail_261_ = lean_ctor_get(v_x_259_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_283_ == 0)
{
v___x_263_ = v_x_259_;
v_isShared_264_ = v_isSharedCheck_283_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_tail_261_);
lean_inc(v_head_260_);
lean_dec(v_x_259_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_283_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_before_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_281_; 
v_before_265_ = lean_ctor_get(v_head_260_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v_head_260_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v_head_260_, 1);
lean_dec(v_unused_282_);
v___x_267_ = v_head_260_;
v_isShared_268_ = v_isSharedCheck_281_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_before_265_);
lean_dec(v_head_260_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_281_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_268_ == 0)
{
lean_ctor_set_tag(v___x_267_, 7);
lean_ctor_set(v___x_267_, 1, v___x_269_);
lean_ctor_set(v___x_267_, 0, v_x_258_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_x_258_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_269_);
v___x_271_ = v_reuseFailAlloc_280_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3);
if (v_isShared_264_ == 0)
{
lean_ctor_set_tag(v___x_263_, 7);
lean_ctor_set(v___x_263_, 1, v___x_272_);
lean_ctor_set(v___x_263_, 0, v___x_271_);
v___x_274_ = v___x_263_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_279_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = l_Lean_MessageData_ofSyntax(v_before_265_);
v___x_276_ = l_Lean_indentD(v___x_275_);
v___x_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_274_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v_x_258_ = v___x_277_;
v_x_259_ = v_tail_261_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_opts_284_, lean_object* v_opt_285_){
_start:
{
lean_object* v_name_286_; lean_object* v_defValue_287_; lean_object* v_map_288_; lean_object* v___x_289_; 
v_name_286_ = lean_ctor_get(v_opt_285_, 0);
v_defValue_287_ = lean_ctor_get(v_opt_285_, 1);
v_map_288_ = lean_ctor_get(v_opts_284_, 0);
v___x_289_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_288_, v_name_286_);
if (lean_obj_tag(v___x_289_) == 0)
{
uint8_t v___x_290_; 
v___x_290_ = lean_unbox(v_defValue_287_);
return v___x_290_;
}
else
{
lean_object* v_val_291_; 
v_val_291_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v___x_289_, 1);
if (lean_obj_tag(v_val_291_) == 1)
{
uint8_t v_v_292_; 
v_v_292_ = lean_ctor_get_uint8(v_val_291_, 0);
lean_dec_ref_known(v_val_291_, 0);
return v_v_292_;
}
else
{
uint8_t v___x_293_; 
lean_dec(v_val_291_);
v___x_293_ = lean_unbox(v_defValue_287_);
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_opts_294_, lean_object* v_opt_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_294_, v_opt_295_);
lean_dec_ref(v_opt_295_);
lean_dec_ref(v_opts_294_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_302_ = l_Lean_MessageData_ofFormat(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_303_, lean_object* v_macroStack_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_toCold_307_; lean_object* v_options_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_toCold_307_ = lean_ctor_get(v___y_305_, 0);
v_options_308_ = lean_ctor_get(v_toCold_307_, 2);
v___x_309_ = l_Lean_Elab_pp_macroStack;
v___x_310_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(v_options_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_dec(v_macroStack_304_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v_msgData_303_);
return v___x_311_;
}
else
{
if (lean_obj_tag(v_macroStack_304_) == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v_msgData_303_);
return v___x_312_;
}
else
{
lean_object* v_head_313_; lean_object* v_after_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_329_; 
v_head_313_ = lean_ctor_get(v_macroStack_304_, 0);
lean_inc(v_head_313_);
v_after_314_ = lean_ctor_get(v_head_313_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_head_313_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v_head_313_, 0);
lean_dec(v_unused_330_);
v___x_316_ = v_head_313_;
v_isShared_317_ = v_isSharedCheck_329_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_after_314_);
lean_dec(v_head_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_329_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 7);
lean_ctor_set(v___x_316_, 1, v___x_318_);
lean_ctor_set(v___x_316_, 0, v_msgData_303_);
v___x_320_ = v___x_316_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_msgData_303_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_318_);
v___x_320_ = v_reuseFailAlloc_328_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_msgData_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_321_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = l_Lean_MessageData_ofSyntax(v_after_314_);
v___x_324_ = l_Lean_indentD(v___x_323_);
v_msgData_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_325_, 0, v___x_322_);
lean_ctor_set(v_msgData_325_, 1, v___x_324_);
v___x_326_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12(v_msgData_325_, v_macroStack_304_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_331_, lean_object* v_macroStack_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_331_, v_macroStack_332_, v___y_333_);
lean_dec_ref(v___y_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_ref_344_; lean_object* v___x_345_; lean_object* v_a_346_; lean_object* v_macroStack_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_ref_344_ = lean_ctor_get(v___y_341_, 2);
v___x_345_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msg_336_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref(v___x_345_);
v_macroStack_347_ = lean_ctor_get(v___y_337_, 1);
v___x_348_ = l_Lean_Elab_getBetterRef(v_ref_344_, v_macroStack_347_);
lean_inc(v_macroStack_347_);
v___x_349_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_346_, v_macroStack_347_, v___y_341_);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_348_);
lean_ctor_set(v___x_354_, 1, v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 1);
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v_msg_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_367_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__0));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__2));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_377_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__6));
v___x_378_ = lean_unsigned_to_nat(11u);
v___x_379_ = lean_unsigned_to_nat(122u);
v___x_380_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__5));
v___x_381_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__4));
v___x_382_ = l_mkPanicMessageWithDecl(v___x_381_, v___x_380_, v___x_379_, v___x_378_, v___x_377_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(lean_object* v_constName_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_399_; lean_object* v_env_400_; uint8_t v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_st_ref_get(v___y_389_);
v_env_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc_ref(v_env_400_);
lean_dec(v___x_399_);
v___x_401_ = 0;
lean_inc(v_constName_383_);
v___x_402_ = l_Lean_Environment_findAsync_x3f(v_env_400_, v_constName_383_, v___x_401_);
if (lean_obj_tag(v___x_402_) == 1)
{
lean_object* v_val_403_; uint8_t v_kind_404_; 
v_val_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v___x_402_, 1);
v_kind_404_ = lean_ctor_get_uint8(v_val_403_, sizeof(void*)*3);
if (v_kind_404_ == 6)
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_403_);
if (lean_obj_tag(v___x_405_) == 6)
{
lean_object* v_val_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec(v_constName_383_);
v_val_406_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_val_406_);
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 0);
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_val_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v___x_405_);
v___x_414_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7);
v___x_415_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(v___x_414_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_424_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_424_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
if (lean_obj_tag(v_a_416_) == 0)
{
lean_del_object(v___x_418_);
goto v___jp_391_;
}
else
{
lean_object* v_val_420_; lean_object* v___x_422_; 
lean_dec(v_constName_383_);
v_val_420_ = lean_ctor_get(v_a_416_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v_a_416_, 1);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v_val_420_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_val_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec(v_constName_383_);
v_a_425_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_415_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_415_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
else
{
lean_dec(v_val_403_);
goto v___jp_391_;
}
}
else
{
lean_dec(v___x_402_);
goto v___jp_391_;
}
v___jp_391_:
{
lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_392_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1);
v___x_393_ = 0;
v___x_394_ = l_Lean_MessageData_ofConstName(v_constName_383_, v___x_393_);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_392_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v___x_397_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___boxed(lean_object* v_constName_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(v_constName_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(size_t v_sz_442_, size_t v_i_443_, lean_object* v_bs_444_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = lean_usize_dec_lt(v_i_443_, v_sz_442_);
if (v___x_445_ == 0)
{
return v_bs_444_;
}
else
{
lean_object* v_v_446_; lean_object* v___x_447_; lean_object* v_bs_x27_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v_v_446_ = lean_array_uget(v_bs_444_, v_i_443_);
v___x_447_ = lean_unsigned_to_nat(0u);
v_bs_x27_448_ = lean_array_uset(v_bs_444_, v_i_443_, v___x_447_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_443_, v___x_449_);
v___x_451_ = lean_array_uset(v_bs_x27_448_, v_i_443_, v_v_446_);
v_i_443_ = v___x_450_;
v_bs_444_ = v___x_451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1___boxed(lean_object* v_sz_453_, lean_object* v_i_454_, lean_object* v_bs_455_){
_start:
{
size_t v_sz_boxed_456_; size_t v_i_boxed_457_; lean_object* v_res_458_; 
v_sz_boxed_456_ = lean_unbox_usize(v_sz_453_);
lean_dec(v_sz_453_);
v_i_boxed_457_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_res_458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_boxed_456_, v_i_boxed_457_, v_bs_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(lean_object* v_upperBound_469_, lean_object* v_a_470_, lean_object* v_b_471_, lean_object* v___y_472_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = lean_nat_dec_lt(v_a_470_, v_upperBound_469_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
lean_dec(v_a_470_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v_b_471_);
return v___x_475_;
}
else
{
lean_object* v_ref_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_ref_476_ = lean_ctor_get(v___y_472_, 2);
v___x_477_ = 0;
v___x_478_ = l_Lean_SourceInfo_fromRef(v_ref_476_, v___x_477_);
v___x_479_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4));
v___x_480_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__5));
lean_inc(v___x_478_);
v___x_481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_478_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = l_Lean_Syntax_node1(v___x_478_, v___x_479_, v___x_481_);
v___x_483_ = lean_array_push(v_b_471_, v___x_482_);
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_a_470_, v___x_484_);
lean_dec(v_a_470_);
v_a_470_ = v___x_485_;
v_b_471_ = v___x_483_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___boxed(lean_object* v_upperBound_487_, lean_object* v_a_488_, lean_object* v_b_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_upperBound_487_, v_a_488_, v_b_489_, v___y_490_);
lean_dec_ref(v___y_490_);
lean_dec(v_upperBound_487_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(lean_object* v_declName_493_, lean_object* v_as_494_, lean_object* v_j_495_){
_start:
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_array_get_size(v_as_494_);
v___x_497_ = lean_nat_dec_lt(v_j_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_dec(v_j_495_);
v___x_498_ = lean_box(0);
return v___x_498_;
}
else
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_array_fget_borrowed(v_as_494_, v_j_495_);
v___x_500_ = lean_name_eq(v___x_499_, v_declName_493_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v_j_495_, v___x_501_);
lean_dec(v_j_495_);
v_j_495_ = v___x_502_;
goto _start;
}
else
{
lean_object* v___x_504_; 
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v_j_495_);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___boxed(lean_object* v_declName_505_, lean_object* v_as_506_, lean_object* v_j_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(v_declName_505_, v_as_506_, v_j_507_);
lean_dec_ref(v_as_506_);
lean_dec(v_declName_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_ref_516_; uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_ref_516_ = lean_ctor_get(v___y_513_, 2);
v___x_517_ = 0;
v___x_518_ = l_Lean_SourceInfo_fromRef(v_ref_516_, v___x_517_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0___boxed(lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_527_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__4));
v___x_539_ = l_String_toRawSubstring_x27(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18));
v___x_569_ = l_String_toRawSubstring_x27(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36));
v___x_612_ = l_String_toRawSubstring_x27(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(lean_object* v_upperBound_625_, lean_object* v___x_626_, lean_object* v_xs_627_, lean_object* v_allIndVals_628_, lean_object* v_ctx_629_, lean_object* v_a_630_, lean_object* v_b_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_a_640_; uint8_t v___x_644_; 
v___x_644_ = lean_nat_dec_lt(v_a_630_, v_upperBound_625_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec(v_a_630_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v_b_631_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1));
v___x_647_ = l_Lean_Core_mkFreshUserName(v___x_646_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = l_Lean_instInhabitedExpr;
v___x_650_ = lean_nat_add(v___x_626_, v_a_630_);
v___x_651_ = lean_array_get_borrowed(v___x_649_, v_xs_627_, v___x_650_);
lean_dec(v___x_650_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc(v___x_651_);
v___x_652_ = lean_infer_type(v___x_651_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
v___x_654_ = lean_whnf(v_a_653_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v_fst_656_; lean_object* v_snd_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_807_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v_fst_656_ = lean_ctor_get(v_b_631_, 0);
v_snd_657_ = lean_ctor_get(v_b_631_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_b_631_);
if (v_isSharedCheck_807_ == 0)
{
v___x_659_ = v_b_631_;
v_isShared_660_ = v_isSharedCheck_807_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snd_657_);
lean_inc(v_fst_656_);
lean_dec(v_b_631_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_807_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = l_Lean_mkIdent(v_a_648_);
lean_inc(v___x_661_);
v___x_662_ = lean_array_push(v_fst_656_, v___x_661_);
v___x_663_ = l_Lean_Expr_getAppFn(v_a_655_);
lean_dec(v_a_655_);
if (lean_obj_tag(v___x_663_) == 4)
{
lean_object* v_declName_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_declName_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_declName_664_);
lean_dec_ref_known(v___x_663_, 2);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(v_declName_664_, v_allIndVals_628_, v___x_665_);
lean_dec(v_declName_664_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_667_; 
v___x_667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_toCold_668_; lean_object* v_a_669_; lean_object* v_quotContext_670_; lean_object* v_currMacroScope_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v_toCold_668_ = lean_ctor_get(v___y_636_, 0);
v_a_669_ = lean_ctor_get(v___x_667_, 0);
lean_inc_n(v_a_669_, 12);
lean_dec_ref_known(v___x_667_, 1);
v_quotContext_670_ = lean_ctor_get(v_toCold_668_, 8);
v_currMacroScope_671_ = lean_ctor_get(v_toCold_668_, 9);
v___x_672_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3));
v___x_673_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5);
v___x_674_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6));
lean_inc_n(v_currMacroScope_671_, 3);
lean_inc_n(v_quotContext_670_, 3);
v___x_675_ = l_Lean_addMacroScope(v_quotContext_670_, v___x_674_, v_currMacroScope_671_);
v___x_676_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8));
v___x_677_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_677_, 0, v_a_669_);
lean_ctor_set(v___x_677_, 1, v___x_673_);
lean_ctor_set(v___x_677_, 2, v___x_675_);
lean_ctor_set(v___x_677_, 3, v___x_676_);
v___x_678_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_679_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12));
v___x_680_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14));
v___x_681_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15));
v___x_682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_682_, 0, v_a_669_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17));
v___x_684_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19);
v___x_685_ = lean_box(0);
v___x_686_ = l_Lean_addMacroScope(v_quotContext_670_, v___x_685_, v_currMacroScope_671_);
v___x_687_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35));
v___x_688_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_688_, 0, v_a_669_);
lean_ctor_set(v___x_688_, 1, v___x_684_);
lean_ctor_set(v___x_688_, 2, v___x_686_);
lean_ctor_set(v___x_688_, 3, v___x_687_);
v___x_689_ = l_Lean_Syntax_node1(v_a_669_, v___x_683_, v___x_688_);
v___x_690_ = l_Lean_Syntax_node2(v_a_669_, v___x_680_, v___x_682_, v___x_689_);
v___x_691_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37);
v___x_692_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38));
v___x_693_ = l_Lean_addMacroScope(v_quotContext_670_, v___x_692_, v_currMacroScope_671_);
v___x_694_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41));
v___x_695_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_695_, 0, v_a_669_);
lean_ctor_set(v___x_695_, 1, v___x_691_);
lean_ctor_set(v___x_695_, 2, v___x_693_);
lean_ctor_set(v___x_695_, 3, v___x_694_);
v___x_696_ = l_Lean_Syntax_node1(v_a_669_, v___x_678_, v___x_661_);
v___x_697_ = l_Lean_Syntax_node2(v_a_669_, v___x_672_, v___x_695_, v___x_696_);
v___x_698_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42));
v___x_699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_699_, 0, v_a_669_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = l_Lean_Syntax_node3(v_a_669_, v___x_679_, v___x_690_, v___x_697_, v___x_699_);
v___x_701_ = l_Lean_Syntax_node2(v_a_669_, v___x_678_, v_snd_657_, v___x_700_);
v___x_702_ = l_Lean_Syntax_node2(v_a_669_, v___x_672_, v___x_677_, v___x_701_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_702_);
lean_ctor_set(v___x_659_, 0, v___x_662_);
v___x_704_ = v___x_659_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
v_a_640_ = v___x_704_;
goto v___jp_639_;
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v___x_662_);
lean_dec(v___x_661_);
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_a_630_);
v_a_706_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_667_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_667_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_val_714_; lean_object* v___x_715_; 
v_val_714_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v___x_666_, 1);
v___x_715_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_toCold_716_; lean_object* v_a_717_; lean_object* v_quotContext_718_; lean_object* v_currMacroScope_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_auxFunNames_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v_toCold_716_ = lean_ctor_get(v___y_636_, 0);
v_a_717_ = lean_ctor_get(v___x_715_, 0);
lean_inc_n(v_a_717_, 11);
lean_dec_ref_known(v___x_715_, 1);
v_quotContext_718_ = lean_ctor_get(v_toCold_716_, 8);
v_currMacroScope_719_ = lean_ctor_get(v_toCold_716_, 9);
v___x_720_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3));
v___x_721_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5);
v___x_722_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6));
lean_inc_n(v_currMacroScope_719_, 2);
lean_inc_n(v_quotContext_718_, 2);
v___x_723_ = l_Lean_addMacroScope(v_quotContext_718_, v___x_722_, v_currMacroScope_719_);
v___x_724_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8));
v___x_725_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_725_, 0, v_a_717_);
lean_ctor_set(v___x_725_, 1, v___x_721_);
lean_ctor_set(v___x_725_, 2, v___x_723_);
lean_ctor_set(v___x_725_, 3, v___x_724_);
v___x_726_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12));
v___x_727_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14));
v___x_728_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15));
v___x_729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_729_, 0, v_a_717_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19);
v___x_731_ = lean_box(0);
v___x_732_ = l_Lean_addMacroScope(v_quotContext_718_, v___x_731_, v_currMacroScope_719_);
v___x_733_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35));
v___x_734_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_734_, 0, v_a_717_);
lean_ctor_set(v___x_734_, 1, v___x_730_);
lean_ctor_set(v___x_734_, 2, v___x_732_);
lean_ctor_set(v___x_734_, 3, v___x_733_);
v_auxFunNames_735_ = lean_ctor_get(v_ctx_629_, 2);
v___x_736_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17));
v___x_737_ = l_Lean_Syntax_node1(v_a_717_, v___x_736_, v___x_734_);
v___x_738_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_739_ = l_Lean_Syntax_node2(v_a_717_, v___x_727_, v___x_729_, v___x_737_);
v___x_740_ = lean_array_get_borrowed(v___x_731_, v_auxFunNames_735_, v_val_714_);
lean_dec(v_val_714_);
lean_inc(v___x_740_);
v___x_741_ = l_Lean_mkIdent(v___x_740_);
v___x_742_ = l_Lean_Syntax_node1(v_a_717_, v___x_738_, v___x_661_);
v___x_743_ = l_Lean_Syntax_node2(v_a_717_, v___x_720_, v___x_741_, v___x_742_);
v___x_744_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42));
v___x_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_745_, 0, v_a_717_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Lean_Syntax_node3(v_a_717_, v___x_726_, v___x_739_, v___x_743_, v___x_745_);
v___x_747_ = l_Lean_Syntax_node2(v_a_717_, v___x_738_, v_snd_657_, v___x_746_);
v___x_748_ = l_Lean_Syntax_node2(v_a_717_, v___x_720_, v___x_725_, v___x_747_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_748_);
lean_ctor_set(v___x_659_, 0, v___x_662_);
v___x_750_ = v___x_659_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
v_a_640_ = v___x_750_;
goto v___jp_639_;
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_val_714_);
lean_dec_ref(v___x_662_);
lean_dec(v___x_661_);
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_a_630_);
v_a_752_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_715_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_715_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
else
{
lean_object* v___x_760_; 
lean_dec_ref(v___x_663_);
v___x_760_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_toCold_761_; lean_object* v_a_762_; lean_object* v_quotContext_763_; lean_object* v_currMacroScope_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v_toCold_761_ = lean_ctor_get(v___y_636_, 0);
v_a_762_ = lean_ctor_get(v___x_760_, 0);
lean_inc_n(v_a_762_, 12);
lean_dec_ref_known(v___x_760_, 1);
v_quotContext_763_ = lean_ctor_get(v_toCold_761_, 8);
v_currMacroScope_764_ = lean_ctor_get(v_toCold_761_, 9);
v___x_765_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3));
v___x_766_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5);
v___x_767_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6));
lean_inc_n(v_currMacroScope_764_, 3);
lean_inc_n(v_quotContext_763_, 3);
v___x_768_ = l_Lean_addMacroScope(v_quotContext_763_, v___x_767_, v_currMacroScope_764_);
v___x_769_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8));
v___x_770_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_770_, 0, v_a_762_);
lean_ctor_set(v___x_770_, 1, v___x_766_);
lean_ctor_set(v___x_770_, 2, v___x_768_);
lean_ctor_set(v___x_770_, 3, v___x_769_);
v___x_771_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_772_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12));
v___x_773_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14));
v___x_774_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15));
v___x_775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_775_, 0, v_a_762_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17));
v___x_777_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19);
v___x_778_ = lean_box(0);
v___x_779_ = l_Lean_addMacroScope(v_quotContext_763_, v___x_778_, v_currMacroScope_764_);
v___x_780_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35));
v___x_781_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_781_, 0, v_a_762_);
lean_ctor_set(v___x_781_, 1, v___x_777_);
lean_ctor_set(v___x_781_, 2, v___x_779_);
lean_ctor_set(v___x_781_, 3, v___x_780_);
v___x_782_ = l_Lean_Syntax_node1(v_a_762_, v___x_776_, v___x_781_);
v___x_783_ = l_Lean_Syntax_node2(v_a_762_, v___x_773_, v___x_775_, v___x_782_);
v___x_784_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37);
v___x_785_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38));
v___x_786_ = l_Lean_addMacroScope(v_quotContext_763_, v___x_785_, v_currMacroScope_764_);
v___x_787_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41));
v___x_788_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_788_, 0, v_a_762_);
lean_ctor_set(v___x_788_, 1, v___x_784_);
lean_ctor_set(v___x_788_, 2, v___x_786_);
lean_ctor_set(v___x_788_, 3, v___x_787_);
v___x_789_ = l_Lean_Syntax_node1(v_a_762_, v___x_771_, v___x_661_);
v___x_790_ = l_Lean_Syntax_node2(v_a_762_, v___x_765_, v___x_788_, v___x_789_);
v___x_791_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42));
v___x_792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_792_, 0, v_a_762_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l_Lean_Syntax_node3(v_a_762_, v___x_772_, v___x_783_, v___x_790_, v___x_792_);
v___x_794_ = l_Lean_Syntax_node2(v_a_762_, v___x_771_, v_snd_657_, v___x_793_);
v___x_795_ = l_Lean_Syntax_node2(v_a_762_, v___x_765_, v___x_770_, v___x_794_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_795_);
lean_ctor_set(v___x_659_, 0, v___x_662_);
v___x_797_ = v___x_659_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
v_a_640_ = v___x_797_;
goto v___jp_639_;
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v___x_662_);
lean_dec(v___x_661_);
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_a_630_);
v_a_799_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_760_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_760_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_a_648_);
lean_dec_ref(v_b_631_);
lean_dec(v_a_630_);
v_a_808_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_654_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_654_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_a_648_);
lean_dec_ref(v_b_631_);
lean_dec(v_a_630_);
v_a_816_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_652_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_652_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec_ref(v_b_631_);
lean_dec(v_a_630_);
v_a_824_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_647_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_647_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
v___jp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_add(v_a_630_, v___x_641_);
lean_dec(v_a_630_);
v_a_630_ = v___x_642_;
v_b_631_ = v_a_640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_832_, lean_object* v___x_833_, lean_object* v_xs_834_, lean_object* v_allIndVals_835_, lean_object* v_ctx_836_, lean_object* v_a_837_, lean_object* v_b_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_upperBound_832_, v___x_833_, v_xs_834_, v_allIndVals_835_, v_ctx_836_, v_a_837_, v_b_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec_ref(v_ctx_836_);
lean_dec_ref(v_allIndVals_835_);
lean_dec_ref(v_xs_834_);
lean_dec(v___x_833_);
lean_dec(v_upperBound_832_);
return v_res_846_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Array_mkArray0(lean_box(0));
return v___x_854_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__7));
v___x_864_ = l_Lean_mkAtom(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1(lean_object* v_indVal_866_, lean_object* v___x_867_, lean_object* v_alts_868_, lean_object* v_snd_869_, lean_object* v_numFields_870_, lean_object* v_allIndVals_871_, lean_object* v_ctx_872_, lean_object* v___f_873_, lean_object* v_head_874_, lean_object* v_xs_875_, lean_object* v_x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_numParams_884_; lean_object* v_numIndices_885_; lean_object* v___x_886_; 
v_numParams_884_ = lean_ctor_get(v_indVal_866_, 1);
v_numIndices_885_ = lean_ctor_get(v_indVal_866_, 2);
lean_inc_ref(v_alts_868_);
lean_inc(v___x_867_);
v___x_886_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_numIndices_885_, v___x_867_, v_alts_868_, v___y_881_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
lean_inc(v___x_867_);
v___x_888_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_numParams_884_, v___x_867_, v_alts_868_, v___y_881_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = l_Nat_reprFast(v_snd_869_);
v___x_891_ = lean_box(2);
v___x_892_ = l_Lean_Syntax_mkNumLit(v___x_890_, v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_a_889_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_numFields_870_, v_numParams_884_, v_xs_875_, v_allIndVals_871_, v_ctx_872_, v___x_867_, v___x_893_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
lean_inc_ref(v___f_873_);
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
v___x_896_ = lean_apply_7(v___f_873_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
v___x_898_ = lean_apply_7(v___f_873_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_940_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_940_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_940_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_940_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_fst_903_; lean_object* v_snd_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_939_; 
v_fst_903_ = lean_ctor_get(v_a_895_, 0);
v_snd_904_ = lean_ctor_get(v_a_895_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_a_895_);
if (v_isSharedCheck_939_ == 0)
{
v___x_906_ = v_a_895_;
v_isShared_907_ = v_isSharedCheck_939_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_snd_904_);
lean_inc(v_fst_903_);
lean_dec(v_a_895_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_939_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_908_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3));
v___x_909_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0));
lean_inc(v_a_897_);
if (v_isShared_907_ == 0)
{
lean_ctor_set_tag(v___x_906_, 2);
lean_ctor_set(v___x_906_, 1, v___x_909_);
lean_ctor_set(v___x_906_, 0, v_a_897_);
v___x_911_ = v___x_906_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_897_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_909_);
v___x_911_ = v_reuseFailAlloc_938_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; size_t v_sz_924_; size_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_912_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2));
v___x_913_ = l_Lean_mkIdent(v_head_874_);
lean_inc_n(v_a_897_, 2);
v___x_914_ = l_Lean_Syntax_node2(v_a_897_, v___x_912_, v___x_911_, v___x_913_);
v___x_915_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_916_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_917_ = l_Array_append___redArg(v___x_916_, v_fst_903_);
lean_dec(v_fst_903_);
v___x_918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_918_, 0, v_a_897_);
lean_ctor_set(v___x_918_, 1, v___x_915_);
lean_ctor_set(v___x_918_, 2, v___x_917_);
v___x_919_ = l_Lean_Syntax_node2(v_a_897_, v___x_908_, v___x_914_, v___x_918_);
v___x_920_ = lean_array_push(v_a_887_, v___x_919_);
v___x_921_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5));
v___x_922_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__6));
lean_inc_n(v_a_899_, 4);
v___x_923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_923_, 0, v_a_899_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v_sz_924_ = lean_array_size(v___x_920_);
v___x_925_ = ((size_t)0ULL);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_924_, v___x_925_, v___x_920_);
v___x_927_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8);
v___x_928_ = l_Lean_mkSepArray(v___x_926_, v___x_927_);
lean_dec_ref(v___x_926_);
v___x_929_ = l_Array_append___redArg(v___x_916_, v___x_928_);
lean_dec_ref(v___x_928_);
v___x_930_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_930_, 0, v_a_899_);
lean_ctor_set(v___x_930_, 1, v___x_915_);
lean_ctor_set(v___x_930_, 2, v___x_929_);
v___x_931_ = l_Lean_Syntax_node1(v_a_899_, v___x_915_, v___x_930_);
v___x_932_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__9));
v___x_933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_933_, 0, v_a_899_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_Syntax_node4(v_a_899_, v___x_921_, v___x_923_, v___x_931_, v___x_933_, v_snd_904_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_934_);
v___x_936_ = v___x_901_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_a_897_);
lean_dec(v_a_895_);
lean_dec(v_a_887_);
lean_dec(v_head_874_);
v_a_941_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_898_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_898_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_a_895_);
lean_dec(v_a_887_);
lean_dec(v_head_874_);
lean_dec_ref(v___f_873_);
v_a_949_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_896_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_896_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec(v_a_887_);
lean_dec(v_head_874_);
lean_dec_ref(v___f_873_);
v_a_957_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_894_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_894_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec(v_a_887_);
lean_dec(v_head_874_);
lean_dec_ref(v___f_873_);
lean_dec(v_snd_869_);
lean_dec(v___x_867_);
v_a_965_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_888_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_888_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v_head_874_);
lean_dec_ref(v___f_873_);
lean_dec(v_snd_869_);
lean_dec_ref(v_alts_868_);
lean_dec(v___x_867_);
v_a_973_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_886_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_886_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_981_ = _args[0];
lean_object* v___x_982_ = _args[1];
lean_object* v_alts_983_ = _args[2];
lean_object* v_snd_984_ = _args[3];
lean_object* v_numFields_985_ = _args[4];
lean_object* v_allIndVals_986_ = _args[5];
lean_object* v_ctx_987_ = _args[6];
lean_object* v___f_988_ = _args[7];
lean_object* v_head_989_ = _args[8];
lean_object* v_xs_990_ = _args[9];
lean_object* v_x_991_ = _args[10];
lean_object* v___y_992_ = _args[11];
lean_object* v___y_993_ = _args[12];
lean_object* v___y_994_ = _args[13];
lean_object* v___y_995_ = _args[14];
lean_object* v___y_996_ = _args[15];
lean_object* v___y_997_ = _args[16];
lean_object* v___y_998_ = _args[17];
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1(v_indVal_981_, v___x_982_, v_alts_983_, v_snd_984_, v_numFields_985_, v_allIndVals_986_, v_ctx_987_, v___f_988_, v_head_989_, v_xs_990_, v_x_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v_x_991_);
lean_dec_ref(v_xs_990_);
lean_dec_ref(v_ctx_987_);
lean_dec_ref(v_allIndVals_986_);
lean_dec(v_numFields_985_);
lean_dec_ref(v_indVal_981_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0(lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_ref_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_ref_1007_ = lean_ctor_get(v___y_1004_, 2);
v___x_1008_ = 0;
v___x_1009_ = l_Lean_SourceInfo_fromRef(v_ref_1007_, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0___boxed(lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0(v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(lean_object* v_indVal_1022_, lean_object* v_allIndVals_1023_, lean_object* v_ctx_1024_, lean_object* v_as_x27_1025_, lean_object* v_b_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
if (lean_obj_tag(v_as_x27_1025_) == 0)
{
lean_object* v___x_1034_; 
lean_dec_ref(v_ctx_1024_);
lean_dec_ref(v_allIndVals_1023_);
lean_dec_ref(v_indVal_1022_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_b_1026_);
return v___x_1034_;
}
else
{
lean_object* v_head_1035_; lean_object* v_tail_1036_; lean_object* v___x_1037_; 
v_head_1035_ = lean_ctor_get(v_as_x27_1025_, 0);
v_tail_1036_ = lean_ctor_get(v_as_x27_1025_, 1);
lean_inc(v_head_1035_);
v___x_1037_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(v_head_1035_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v_toConstantVal_1039_; lean_object* v_fst_1040_; lean_object* v_snd_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1069_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v_toConstantVal_1039_ = lean_ctor_get(v_a_1038_, 0);
lean_inc_ref(v_toConstantVal_1039_);
v_fst_1040_ = lean_ctor_get(v_b_1026_, 0);
v_snd_1041_ = lean_ctor_get(v_b_1026_, 1);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_b_1026_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1043_ = v_b_1026_;
v_isShared_1044_ = v_isSharedCheck_1069_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_snd_1041_);
lean_inc(v_fst_1040_);
lean_dec(v_b_1026_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1069_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_numFields_1045_; lean_object* v_type_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v_alts_1049_; lean_object* v___f_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; 
v_numFields_1045_ = lean_ctor_get(v_a_1038_, 4);
lean_inc(v_numFields_1045_);
lean_dec(v_a_1038_);
v_type_1046_ = lean_ctor_get(v_toConstantVal_1039_, 2);
lean_inc_ref(v_type_1046_);
lean_dec_ref(v_toConstantVal_1039_);
v___f_1047_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__0));
v___x_1048_ = lean_unsigned_to_nat(0u);
v_alts_1049_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1));
lean_inc(v_head_1035_);
lean_inc_ref(v_ctx_1024_);
lean_inc_ref(v_allIndVals_1023_);
lean_inc(v_snd_1041_);
lean_inc_ref(v_indVal_1022_);
v___f_1050_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___boxed), 18, 9);
lean_closure_set(v___f_1050_, 0, v_indVal_1022_);
lean_closure_set(v___f_1050_, 1, v___x_1048_);
lean_closure_set(v___f_1050_, 2, v_alts_1049_);
lean_closure_set(v___f_1050_, 3, v_snd_1041_);
lean_closure_set(v___f_1050_, 4, v_numFields_1045_);
lean_closure_set(v___f_1050_, 5, v_allIndVals_1023_);
lean_closure_set(v___f_1050_, 6, v_ctx_1024_);
lean_closure_set(v___f_1050_, 7, v___f_1047_);
lean_closure_set(v___f_1050_, 8, v_head_1035_);
v___x_1051_ = 0;
v___x_1052_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_type_1046_, v___f_1050_, v___x_1051_, v___x_1051_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = lean_array_push(v_fst_1040_, v_a_1053_);
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_add(v_snd_1041_, v___x_1055_);
lean_dec(v_snd_1041_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v___x_1056_);
lean_ctor_set(v___x_1043_, 0, v___x_1054_);
v___x_1058_ = v___x_1043_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
v_as_x27_1025_ = v_tail_1036_;
v_b_1026_ = v___x_1058_;
goto _start;
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_del_object(v___x_1043_);
lean_dec(v_snd_1041_);
lean_dec(v_fst_1040_);
lean_dec_ref(v_ctx_1024_);
lean_dec_ref(v_allIndVals_1023_);
lean_dec_ref(v_indVal_1022_);
v_a_1061_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1052_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1052_);
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
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref(v_b_1026_);
lean_dec_ref(v_ctx_1024_);
lean_dec_ref(v_allIndVals_1023_);
lean_dec_ref(v_indVal_1022_);
v_a_1070_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1037_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1037_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___boxed(lean_object* v_indVal_1078_, lean_object* v_allIndVals_1079_, lean_object* v_ctx_1080_, lean_object* v_as_x27_1081_, lean_object* v_b_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(v_indVal_1078_, v_allIndVals_1079_, v_ctx_1080_, v_as_x27_1081_, v_b_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v_as_x27_1081_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7(size_t v_sz_1091_, size_t v_i_1092_, lean_object* v_bs_1093_){
_start:
{
uint8_t v___x_1094_; 
v___x_1094_ = lean_usize_dec_lt(v_i_1092_, v_sz_1091_);
if (v___x_1094_ == 0)
{
return v_bs_1093_;
}
else
{
lean_object* v_v_1095_; lean_object* v___x_1096_; lean_object* v_bs_x27_1097_; size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1100_; 
v_v_1095_ = lean_array_uget(v_bs_1093_, v_i_1092_);
v___x_1096_ = lean_unsigned_to_nat(0u);
v_bs_x27_1097_ = lean_array_uset(v_bs_1093_, v_i_1092_, v___x_1096_);
v___x_1098_ = ((size_t)1ULL);
v___x_1099_ = lean_usize_add(v_i_1092_, v___x_1098_);
v___x_1100_ = lean_array_uset(v_bs_x27_1097_, v_i_1092_, v_v_1095_);
v_i_1092_ = v___x_1099_;
v_bs_1093_ = v___x_1100_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7___boxed(lean_object* v_sz_1102_, lean_object* v_i_1103_, lean_object* v_bs_1104_){
_start:
{
size_t v_sz_boxed_1105_; size_t v_i_boxed_1106_; lean_object* v_res_1107_; 
v_sz_boxed_1105_ = lean_unbox_usize(v_sz_1102_);
lean_dec(v_sz_1102_);
v_i_boxed_1106_ = lean_unbox_usize(v_i_1103_);
lean_dec(v_i_1103_);
v_res_1107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7(v_sz_boxed_1105_, v_i_boxed_1106_, v_bs_1104_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(lean_object* v_ctx_1111_, lean_object* v_indVal_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_all_1120_; lean_object* v_ctors_1121_; lean_object* v_allIndVals_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_all_1120_ = lean_ctor_get(v_indVal_1112_, 3);
v_ctors_1121_ = lean_ctor_get(v_indVal_1112_, 4);
lean_inc(v_ctors_1121_);
lean_inc(v_all_1120_);
v_allIndVals_1122_ = lean_array_mk(v_all_1120_);
v___x_1123_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0));
v___x_1124_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(v_indVal_1112_, v_allIndVals_1122_, v_ctx_1111_, v_ctors_1121_, v___x_1123_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_ctors_1121_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1136_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_fst_1129_; size_t v_sz_1130_; size_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v_fst_1129_ = lean_ctor_get(v_a_1125_, 0);
lean_inc(v_fst_1129_);
lean_dec(v_a_1125_);
v_sz_1130_ = lean_array_size(v_fst_1129_);
v___x_1131_ = ((size_t)0ULL);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7(v_sz_1130_, v___x_1131_, v_fst_1129_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1132_);
v___x_1134_ = v___x_1127_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
v_a_1137_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1124_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1124_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___boxed(lean_object* v_ctx_1145_, lean_object* v_indVal_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(v_ctx_1145_, v_indVal_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3(lean_object* v_upperBound_1155_, lean_object* v___x_1156_, lean_object* v_xs_1157_, lean_object* v_allIndVals_1158_, lean_object* v_ctx_1159_, lean_object* v_inst_1160_, lean_object* v_R_1161_, lean_object* v_a_1162_, lean_object* v_b_1163_, lean_object* v_c_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_upperBound_1155_, v___x_1156_, v_xs_1157_, v_allIndVals_1158_, v_ctx_1159_, v_a_1162_, v_b_1163_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1173_ = _args[0];
lean_object* v___x_1174_ = _args[1];
lean_object* v_xs_1175_ = _args[2];
lean_object* v_allIndVals_1176_ = _args[3];
lean_object* v_ctx_1177_ = _args[4];
lean_object* v_inst_1178_ = _args[5];
lean_object* v_R_1179_ = _args[6];
lean_object* v_a_1180_ = _args[7];
lean_object* v_b_1181_ = _args[8];
lean_object* v_c_1182_ = _args[9];
lean_object* v___y_1183_ = _args[10];
lean_object* v___y_1184_ = _args[11];
lean_object* v___y_1185_ = _args[12];
lean_object* v___y_1186_ = _args[13];
lean_object* v___y_1187_ = _args[14];
lean_object* v___y_1188_ = _args[15];
lean_object* v___y_1189_ = _args[16];
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3(v_upperBound_1173_, v___x_1174_, v_xs_1175_, v_allIndVals_1176_, v_ctx_1177_, v_inst_1178_, v_R_1179_, v_a_1180_, v_b_1181_, v_c_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec_ref(v_ctx_1177_);
lean_dec_ref(v_allIndVals_1176_);
lean_dec_ref(v_xs_1175_);
lean_dec(v___x_1174_);
lean_dec(v_upperBound_1173_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4(lean_object* v_upperBound_1191_, lean_object* v_inst_1192_, lean_object* v_R_1193_, lean_object* v_a_1194_, lean_object* v_b_1195_, lean_object* v_c_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_upperBound_1191_, v_a_1194_, v_b_1195_, v___y_1201_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___boxed(lean_object* v_upperBound_1205_, lean_object* v_inst_1206_, lean_object* v_R_1207_, lean_object* v_a_1208_, lean_object* v_b_1209_, lean_object* v_c_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4(v_upperBound_1205_, v_inst_1206_, v_R_1207_, v_a_1208_, v_b_1209_, v_c_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v_upperBound_1205_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(lean_object* v_indVal_1219_, lean_object* v_allIndVals_1220_, lean_object* v_ctx_1221_, lean_object* v_as_1222_, lean_object* v_as_x27_1223_, lean_object* v_b_1224_, lean_object* v_a_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(v_indVal_1219_, v_allIndVals_1220_, v_ctx_1221_, v_as_x27_1223_, v_b_1224_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___boxed(lean_object* v_indVal_1234_, lean_object* v_allIndVals_1235_, lean_object* v_ctx_1236_, lean_object* v_as_1237_, lean_object* v_as_x27_1238_, lean_object* v_b_1239_, lean_object* v_a_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(v_indVal_1234_, v_allIndVals_1235_, v_ctx_1236_, v_as_1237_, v_as_x27_1238_, v_b_1239_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v_as_x27_1238_);
lean_dec(v_as_1237_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1249_, lean_object* v_msg_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v_msg_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1259_, lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0(v_00_u03b1_1259_, v_msg_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1269_, lean_object* v_macroStack_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1269_, v_macroStack_1270_, v___y_1275_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1279_, lean_object* v_macroStack_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3(v_msgData_1279_, v_macroStack_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch(lean_object* v_ctx_1302_, lean_object* v_header_1303_, lean_object* v_indVal_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; 
lean_inc_ref(v_indVal_1304_);
v___x_1312_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_1303_, v_indVal_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1314_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1314_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(v_ctx_1302_, v_indVal_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1345_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1345_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1345_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_ref_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; size_t v_sz_1328_; size_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v_ref_1319_ = lean_ctor_get(v_a_1309_, 2);
v___x_1320_ = 0;
v___x_1321_ = l_Lean_SourceInfo_fromRef(v_ref_1319_, v___x_1320_);
v___x_1322_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0));
v___x_1323_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1));
lean_inc_n(v___x_1321_, 6);
v___x_1324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1321_);
lean_ctor_set(v___x_1324_, 1, v___x_1322_);
v___x_1325_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_1326_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_1327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1321_);
lean_ctor_set(v___x_1327_, 1, v___x_1325_);
lean_ctor_set(v___x_1327_, 2, v___x_1326_);
v_sz_1328_ = lean_array_size(v_a_1313_);
v___x_1329_ = ((size_t)0ULL);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_1328_, v___x_1329_, v_a_1313_);
v___x_1331_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8);
v___x_1332_ = l_Lean_mkSepArray(v___x_1330_, v___x_1331_);
lean_dec_ref(v___x_1330_);
v___x_1333_ = l_Array_append___redArg(v___x_1326_, v___x_1332_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1321_);
lean_ctor_set(v___x_1334_, 1, v___x_1325_);
lean_ctor_set(v___x_1334_, 2, v___x_1333_);
v___x_1335_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2));
v___x_1336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1321_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4));
v___x_1338_ = l_Array_append___redArg(v___x_1326_, v_a_1315_);
lean_dec(v_a_1315_);
v___x_1339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1321_);
lean_ctor_set(v___x_1339_, 1, v___x_1325_);
lean_ctor_set(v___x_1339_, 2, v___x_1338_);
v___x_1340_ = l_Lean_Syntax_node1(v___x_1321_, v___x_1337_, v___x_1339_);
lean_inc_ref(v___x_1327_);
v___x_1341_ = l_Lean_Syntax_node6(v___x_1321_, v___x_1323_, v___x_1324_, v___x_1327_, v___x_1327_, v___x_1334_, v___x_1336_, v___x_1340_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1341_);
v___x_1343_ = v___x_1317_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_a_1313_);
v_a_1346_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1314_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1314_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_indVal_1304_);
lean_dec_ref(v_ctx_1302_);
v_a_1354_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1312_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1312_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___boxed(lean_object* v_ctx_1362_, lean_object* v_header_1363_, lean_object* v_indVal_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Elab_Deriving_Hashable_mkMatch(v_ctx_1362_, v_header_1363_, v_indVal_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
return v_res_1372_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14));
v___x_1413_ = l_String_toRawSubstring_x27(v___x_1412_);
return v___x_1413_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28));
v___x_1445_ = l_String_toRawSubstring_x27(v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction(lean_object* v_ctx_1491_, lean_object* v_i_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_typeInfos_1500_; lean_object* v_auxFunNames_1501_; uint8_t v_usePartial_1502_; lean_object* v___x_1503_; lean_object* v_indVal_1504_; lean_object* v___x_1505_; 
v_typeInfos_1500_ = lean_ctor_get(v_ctx_1491_, 1);
v_auxFunNames_1501_ = lean_ctor_get(v_ctx_1491_, 2);
v_usePartial_1502_ = lean_ctor_get_uint8(v_ctx_1491_, sizeof(void*)*3);
v___x_1503_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_1504_ = lean_array_get_borrowed(v___x_1503_, v_typeInfos_1500_, v_i_1492_);
lean_inc(v_indVal_1504_);
v___x_1505_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader(v_indVal_1504_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc_n(v_a_1506_, 2);
lean_dec_ref_known(v___x_1505_, 1);
lean_inc(v_indVal_1504_);
lean_inc_ref(v_ctx_1491_);
v___x_1507_ = l_Lean_Elab_Deriving_Hashable_mkMatch(v_ctx_1491_, v_a_1506_, v_indVal_1504_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1660_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1660_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1660_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v_auxFunName_1513_; lean_object* v_body_1515_; lean_object* v___y_1516_; 
v___x_1512_ = lean_box(0);
v_auxFunName_1513_ = lean_array_get(v___x_1512_, v_auxFunNames_1501_, v_i_1492_);
if (v_usePartial_1502_ == 0)
{
lean_dec_ref(v_ctx_1491_);
v_body_1515_ = v_a_1508_;
v___y_1516_ = v_a_1497_;
goto v___jp_1514_;
}
else
{
lean_object* v_argNames_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_argNames_1646_ = lean_ctor_get(v_a_1506_, 1);
v___x_1647_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1));
lean_inc_ref(v_argNames_1646_);
v___x_1648_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_1491_, v___x_1647_, v_argNames_1646_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
lean_dec_ref(v_ctx_1491_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = l_Lean_Elab_Deriving_mkLet(v_a_1649_, v_a_1508_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
lean_dec(v_a_1649_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v_body_1515_ = v_a_1651_;
v___y_1516_ = v_a_1497_;
goto v___jp_1514_;
}
else
{
lean_dec(v_auxFunName_1513_);
lean_del_object(v___x_1510_);
lean_dec(v_a_1506_);
return v___x_1650_;
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_auxFunName_1513_);
lean_del_object(v___x_1510_);
lean_dec(v_a_1508_);
lean_dec(v_a_1506_);
v_a_1652_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1648_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1648_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
v___jp_1514_:
{
if (v_usePartial_1502_ == 0)
{
lean_object* v_toCold_1517_; lean_object* v_binders_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1584_; 
v_toCold_1517_ = lean_ctor_get(v___y_1516_, 0);
v_binders_1518_ = lean_ctor_get(v_a_1506_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_a_1506_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; lean_object* v_unused_1586_; lean_object* v_unused_1587_; 
v_unused_1585_ = lean_ctor_get(v_a_1506_, 3);
lean_dec(v_unused_1585_);
v_unused_1586_ = lean_ctor_get(v_a_1506_, 2);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v_a_1506_, 1);
lean_dec(v_unused_1587_);
v___x_1520_ = v_a_1506_;
v_isShared_1521_ = v_isSharedCheck_1584_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_binders_1518_);
lean_dec(v_a_1506_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1584_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_ref_1522_; lean_object* v_quotContext_1523_; lean_object* v_currMacroScope_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v_ref_1522_ = lean_ctor_get(v___y_1516_, 2);
v_quotContext_1523_ = lean_ctor_get(v_toCold_1517_, 8);
v_currMacroScope_1524_ = lean_ctor_get(v_toCold_1517_, 9);
v___x_1525_ = l_Lean_SourceInfo_fromRef(v_ref_1522_, v_usePartial_1502_);
v___x_1526_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1));
v___x_1527_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3));
v___x_1528_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_1529_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
lean_inc_n(v___x_1525_, 4);
v___x_1530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1525_);
lean_ctor_set(v___x_1530_, 1, v___x_1528_);
lean_ctor_set(v___x_1530_, 2, v___x_1529_);
v___x_1531_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5));
v___x_1532_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6));
v___x_1533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1525_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8));
v___x_1535_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10));
lean_inc_ref(v___x_1530_);
v___x_1536_ = l_Lean_Syntax_node1(v___x_1525_, v___x_1535_, v___x_1530_);
v___x_1537_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13));
v___x_1538_ = lean_obj_once(&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15, &l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15_once, _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15);
v___x_1539_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__16));
lean_inc(v_currMacroScope_1524_);
lean_inc(v_quotContext_1523_);
v___x_1540_ = l_Lean_addMacroScope(v_quotContext_1523_, v___x_1539_, v_currMacroScope_1524_);
v___x_1541_ = lean_box(0);
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 3);
lean_ctor_set(v___x_1520_, 3, v___x_1541_);
lean_ctor_set(v___x_1520_, 2, v___x_1540_);
lean_ctor_set(v___x_1520_, 1, v___x_1538_);
lean_ctor_set(v___x_1520_, 0, v___x_1525_);
v___x_1543_ = v___x_1520_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_inc_ref_n(v___x_1530_, 11);
lean_inc_n(v___x_1525_, 19);
v___x_1544_ = l_Lean_Syntax_node2(v___x_1525_, v___x_1537_, v___x_1543_, v___x_1530_);
v___x_1545_ = l_Lean_Syntax_node2(v___x_1525_, v___x_1534_, v___x_1536_, v___x_1544_);
v___x_1546_ = l_Lean_Syntax_node1(v___x_1525_, v___x_1528_, v___x_1545_);
v___x_1547_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__17));
v___x_1548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1525_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Lean_Syntax_node3(v___x_1525_, v___x_1531_, v___x_1533_, v___x_1546_, v___x_1548_);
v___x_1550_ = l_Lean_Syntax_node1(v___x_1525_, v___x_1528_, v___x_1549_);
v___x_1551_ = l_Lean_Syntax_node7(v___x_1525_, v___x_1527_, v___x_1530_, v___x_1550_, v___x_1530_, v___x_1530_, v___x_1530_, v___x_1530_, v___x_1530_);
v___x_1552_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19));
v___x_1553_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20));
v___x_1554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1525_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22));
v___x_1556_ = l_Lean_mkIdent(v_auxFunName_1513_);
v___x_1557_ = l_Lean_Syntax_node2(v___x_1525_, v___x_1555_, v___x_1556_, v___x_1530_);
v___x_1558_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24));
v___x_1559_ = l_Array_append___redArg(v___x_1529_, v_binders_1518_);
lean_dec_ref(v_binders_1518_);
v___x_1560_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1525_);
lean_ctor_set(v___x_1560_, 1, v___x_1528_);
lean_ctor_set(v___x_1560_, 2, v___x_1559_);
v___x_1561_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26));
v___x_1562_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27));
v___x_1563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1525_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_obj_once(&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29, &l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29_once, _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29);
v___x_1565_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30));
lean_inc(v_currMacroScope_1524_);
lean_inc(v_quotContext_1523_);
v___x_1566_ = l_Lean_addMacroScope(v_quotContext_1523_, v___x_1565_, v_currMacroScope_1524_);
v___x_1567_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35));
v___x_1568_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1525_);
lean_ctor_set(v___x_1568_, 1, v___x_1564_);
lean_ctor_set(v___x_1568_, 2, v___x_1566_);
lean_ctor_set(v___x_1568_, 3, v___x_1567_);
v___x_1569_ = l_Lean_Syntax_node2(v___x_1525_, v___x_1561_, v___x_1563_, v___x_1568_);
v___x_1570_ = l_Lean_Syntax_node1(v___x_1525_, v___x_1528_, v___x_1569_);
v___x_1571_ = l_Lean_Syntax_node2(v___x_1525_, v___x_1558_, v___x_1560_, v___x_1570_);
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37));
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38));
v___x_1574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1525_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41));
v___x_1576_ = l_Lean_Syntax_node2(v___x_1525_, v___x_1575_, v___x_1530_, v___x_1530_);
v___x_1577_ = l_Lean_Syntax_node4(v___x_1525_, v___x_1572_, v___x_1574_, v_body_1515_, v___x_1576_, v___x_1530_);
v___x_1578_ = l_Lean_Syntax_node5(v___x_1525_, v___x_1552_, v___x_1554_, v___x_1557_, v___x_1571_, v___x_1577_, v___x_1530_);
v___x_1579_ = l_Lean_Syntax_node2(v___x_1525_, v___x_1526_, v___x_1551_, v___x_1578_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1579_);
v___x_1581_ = v___x_1510_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v_toCold_1588_; lean_object* v_binders_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1642_; 
v_toCold_1588_ = lean_ctor_get(v___y_1516_, 0);
v_binders_1589_ = lean_ctor_get(v_a_1506_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_a_1506_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; lean_object* v_unused_1644_; lean_object* v_unused_1645_; 
v_unused_1643_ = lean_ctor_get(v_a_1506_, 3);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_a_1506_, 2);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_a_1506_, 1);
lean_dec(v_unused_1645_);
v___x_1591_ = v_a_1506_;
v_isShared_1592_ = v_isSharedCheck_1642_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_binders_1589_);
lean_dec(v_a_1506_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1642_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v_ref_1593_; lean_object* v_quotContext_1594_; lean_object* v_currMacroScope_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v_ref_1593_ = lean_ctor_get(v___y_1516_, 2);
v_quotContext_1594_ = lean_ctor_get(v_toCold_1588_, 8);
v_currMacroScope_1595_ = lean_ctor_get(v_toCold_1588_, 9);
v___x_1596_ = 0;
v___x_1597_ = l_Lean_SourceInfo_fromRef(v_ref_1593_, v___x_1596_);
v___x_1598_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1));
v___x_1599_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3));
v___x_1600_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_1601_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
lean_inc_n(v___x_1597_, 10);
v___x_1602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1597_);
lean_ctor_set(v___x_1602_, 1, v___x_1600_);
lean_ctor_set(v___x_1602_, 2, v___x_1601_);
v___x_1603_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42));
v___x_1604_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43));
v___x_1605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1597_);
lean_ctor_set(v___x_1605_, 1, v___x_1603_);
v___x_1606_ = l_Lean_Syntax_node1(v___x_1597_, v___x_1604_, v___x_1605_);
v___x_1607_ = l_Lean_Syntax_node1(v___x_1597_, v___x_1600_, v___x_1606_);
lean_inc_ref_n(v___x_1602_, 7);
v___x_1608_ = l_Lean_Syntax_node7(v___x_1597_, v___x_1599_, v___x_1602_, v___x_1602_, v___x_1602_, v___x_1602_, v___x_1602_, v___x_1602_, v___x_1607_);
v___x_1609_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19));
v___x_1610_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20));
v___x_1611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1597_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22));
v___x_1613_ = l_Lean_mkIdent(v_auxFunName_1513_);
v___x_1614_ = l_Lean_Syntax_node2(v___x_1597_, v___x_1612_, v___x_1613_, v___x_1602_);
v___x_1615_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24));
v___x_1616_ = l_Array_append___redArg(v___x_1601_, v_binders_1589_);
lean_dec_ref(v_binders_1589_);
v___x_1617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1597_);
lean_ctor_set(v___x_1617_, 1, v___x_1600_);
lean_ctor_set(v___x_1617_, 2, v___x_1616_);
v___x_1618_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26));
v___x_1619_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27));
v___x_1620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1597_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = lean_obj_once(&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29, &l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29_once, _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29);
v___x_1622_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30));
lean_inc(v_currMacroScope_1595_);
lean_inc(v_quotContext_1594_);
v___x_1623_ = l_Lean_addMacroScope(v_quotContext_1594_, v___x_1622_, v_currMacroScope_1595_);
v___x_1624_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__46));
if (v_isShared_1592_ == 0)
{
lean_ctor_set_tag(v___x_1591_, 3);
lean_ctor_set(v___x_1591_, 3, v___x_1624_);
lean_ctor_set(v___x_1591_, 2, v___x_1623_);
lean_ctor_set(v___x_1591_, 1, v___x_1621_);
lean_ctor_set(v___x_1591_, 0, v___x_1597_);
v___x_1626_ = v___x_1591_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
lean_inc_n(v___x_1597_, 7);
v___x_1627_ = l_Lean_Syntax_node2(v___x_1597_, v___x_1618_, v___x_1620_, v___x_1626_);
v___x_1628_ = l_Lean_Syntax_node1(v___x_1597_, v___x_1600_, v___x_1627_);
v___x_1629_ = l_Lean_Syntax_node2(v___x_1597_, v___x_1615_, v___x_1617_, v___x_1628_);
v___x_1630_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37));
v___x_1631_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38));
v___x_1632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1597_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41));
lean_inc_ref_n(v___x_1602_, 3);
v___x_1634_ = l_Lean_Syntax_node2(v___x_1597_, v___x_1633_, v___x_1602_, v___x_1602_);
v___x_1635_ = l_Lean_Syntax_node4(v___x_1597_, v___x_1630_, v___x_1632_, v_body_1515_, v___x_1634_, v___x_1602_);
v___x_1636_ = l_Lean_Syntax_node5(v___x_1597_, v___x_1609_, v___x_1611_, v___x_1614_, v___x_1629_, v___x_1635_, v___x_1602_);
v___x_1637_ = l_Lean_Syntax_node2(v___x_1597_, v___x_1598_, v___x_1608_, v___x_1636_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1637_);
v___x_1639_ = v___x_1510_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1506_);
lean_dec_ref(v_ctx_1491_);
return v___x_1507_;
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v_ctx_1491_);
v_a_1661_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1505_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1505_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___boxed(lean_object* v_ctx_1669_, lean_object* v_i_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction(v_ctx_1669_, v_i_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_i_1670_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(lean_object* v_upperBound_1679_, lean_object* v_ctx_1680_, lean_object* v_a_1681_, lean_object* v_b_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_nat_dec_lt(v_a_1681_, v_upperBound_1679_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
lean_dec(v_a_1681_);
lean_dec_ref(v_ctx_1680_);
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_b_1682_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; 
lean_inc_ref(v_ctx_1680_);
v___x_1692_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction(v_ctx_1680_, v_a_1681_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = lean_array_push(v_b_1682_, v_a_1693_);
v___x_1695_ = lean_unsigned_to_nat(1u);
v___x_1696_ = lean_nat_add(v_a_1681_, v___x_1695_);
lean_dec(v_a_1681_);
v_a_1681_ = v___x_1696_;
v_b_1682_ = v___x_1694_;
goto _start;
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref(v_b_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_ctx_1680_);
v_a_1698_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1692_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1692_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg___boxed(lean_object* v_upperBound_1706_, lean_object* v_ctx_1707_, lean_object* v_a_1708_, lean_object* v_b_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v_upperBound_1706_, v_ctx_1707_, v_a_1708_, v_b_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v_upperBound_1706_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs(lean_object* v_ctx_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_typeInfos_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v_auxDefs_1736_; lean_object* v___x_1737_; 
v_typeInfos_1733_ = lean_ctor_get(v_ctx_1725_, 1);
v___x_1734_ = lean_array_get_size(v_typeInfos_1733_);
v___x_1735_ = lean_unsigned_to_nat(0u);
v_auxDefs_1736_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1));
v___x_1737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v___x_1734_, v_ctx_1725_, v___x_1735_, v_auxDefs_1736_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1758_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1758_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1758_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_ref_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v_ref_1742_ = lean_ctor_get(v_a_1730_, 2);
v___x_1743_ = 0;
v___x_1744_ = l_Lean_SourceInfo_fromRef(v_ref_1742_, v___x_1743_);
v___x_1745_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0));
v___x_1746_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1));
lean_inc_n(v___x_1744_, 3);
v___x_1747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1744_);
lean_ctor_set(v___x_1747_, 1, v___x_1745_);
v___x_1748_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10));
v___x_1749_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_1750_ = l_Array_append___redArg(v___x_1749_, v_a_1738_);
lean_dec(v_a_1738_);
v___x_1751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1744_);
lean_ctor_set(v___x_1751_, 1, v___x_1748_);
lean_ctor_set(v___x_1751_, 2, v___x_1750_);
v___x_1752_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2));
v___x_1753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1744_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = l_Lean_Syntax_node3(v___x_1744_, v___x_1746_, v___x_1747_, v___x_1751_, v___x_1753_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1754_);
v___x_1756_ = v___x_1740_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_a_1759_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1737_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1737_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs___boxed(lean_object* v_ctx_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs(v_ctx_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0(lean_object* v_upperBound_1776_, lean_object* v_ctx_1777_, lean_object* v_inst_1778_, lean_object* v_R_1779_, lean_object* v_a_1780_, lean_object* v_b_1781_, lean_object* v_c_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v_upperBound_1776_, v_ctx_1777_, v_a_1780_, v_b_1781_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___boxed(lean_object* v_upperBound_1791_, lean_object* v_ctx_1792_, lean_object* v_inst_1793_, lean_object* v_R_1794_, lean_object* v_a_1795_, lean_object* v_b_1796_, lean_object* v_c_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0(v_upperBound_1791_, v_ctx_1792_, v_inst_1793_, v_R_1794_, v_a_1795_, v_b_1796_, v_c_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v_upperBound_1791_);
return v_res_1805_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1806_; double v___x_1807_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_float_of_nat(v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(lean_object* v_cls_1810_, lean_object* v_msg_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_ref_1817_; lean_object* v___x_1818_; lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1863_; 
v_ref_1817_ = lean_ctor_get(v___y_1814_, 2);
v___x_1818_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msg_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1863_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1863_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v_traceState_1824_; lean_object* v_env_1825_; lean_object* v_nextMacroScope_1826_; lean_object* v_ngen_1827_; lean_object* v_auxDeclNGen_1828_; lean_object* v_cache_1829_; lean_object* v_messages_1830_; lean_object* v_infoState_1831_; lean_object* v_snapshotTasks_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1862_; 
v___x_1823_ = lean_st_ref_take(v___y_1815_);
v_traceState_1824_ = lean_ctor_get(v___x_1823_, 4);
v_env_1825_ = lean_ctor_get(v___x_1823_, 0);
v_nextMacroScope_1826_ = lean_ctor_get(v___x_1823_, 1);
v_ngen_1827_ = lean_ctor_get(v___x_1823_, 2);
v_auxDeclNGen_1828_ = lean_ctor_get(v___x_1823_, 3);
v_cache_1829_ = lean_ctor_get(v___x_1823_, 5);
v_messages_1830_ = lean_ctor_get(v___x_1823_, 6);
v_infoState_1831_ = lean_ctor_get(v___x_1823_, 7);
v_snapshotTasks_1832_ = lean_ctor_get(v___x_1823_, 8);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1834_ = v___x_1823_;
v_isShared_1835_ = v_isSharedCheck_1862_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_snapshotTasks_1832_);
lean_inc(v_infoState_1831_);
lean_inc(v_messages_1830_);
lean_inc(v_cache_1829_);
lean_inc(v_traceState_1824_);
lean_inc(v_auxDeclNGen_1828_);
lean_inc(v_ngen_1827_);
lean_inc(v_nextMacroScope_1826_);
lean_inc(v_env_1825_);
lean_dec(v___x_1823_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1862_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
uint64_t v_tid_1836_; lean_object* v_traces_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1861_; 
v_tid_1836_ = lean_ctor_get_uint64(v_traceState_1824_, sizeof(void*)*1);
v_traces_1837_ = lean_ctor_get(v_traceState_1824_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_traceState_1824_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1839_ = v_traceState_1824_;
v_isShared_1840_ = v_isSharedCheck_1861_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_traces_1837_);
lean_dec(v_traceState_1824_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1861_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; double v___x_1842_; uint8_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0);
v___x_1843_ = 0;
v___x_1844_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18));
v___x_1845_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1845_, 0, v_cls_1810_);
lean_ctor_set(v___x_1845_, 1, v___x_1841_);
lean_ctor_set(v___x_1845_, 2, v___x_1844_);
lean_ctor_set_float(v___x_1845_, sizeof(void*)*3, v___x_1842_);
lean_ctor_set_float(v___x_1845_, sizeof(void*)*3 + 8, v___x_1842_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*3 + 16, v___x_1843_);
v___x_1846_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__1));
v___x_1847_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v_a_1819_);
lean_ctor_set(v___x_1847_, 2, v___x_1846_);
lean_inc(v_ref_1817_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v_ref_1817_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = l_Lean_PersistentArray_push___redArg(v_traces_1837_, v___x_1848_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1849_);
v___x_1851_ = v___x_1839_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1849_);
lean_ctor_set_uint64(v_reuseFailAlloc_1860_, sizeof(void*)*1, v_tid_1836_);
v___x_1851_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 4, v___x_1851_);
v___x_1853_ = v___x_1834_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_env_1825_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_nextMacroScope_1826_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_ngen_1827_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_auxDeclNGen_1828_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1859_, 5, v_cache_1829_);
lean_ctor_set(v_reuseFailAlloc_1859_, 6, v_messages_1830_);
lean_ctor_set(v_reuseFailAlloc_1859_, 7, v_infoState_1831_);
lean_ctor_set(v_reuseFailAlloc_1859_, 8, v_snapshotTasks_1832_);
v___x_1853_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1854_ = lean_st_ref_put(v___y_1815_, v___x_1853_);
v___x_1855_ = lean_box(0);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1855_);
v___x_1857_ = v___x_1821_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_1864_, lean_object* v_msg_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(v_cls_1864_, v_msg_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0(lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
if (lean_obj_tag(v_a_1872_) == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = l_List_reverse___redArg(v_a_1873_);
return v___x_1874_;
}
else
{
lean_object* v_head_1875_; lean_object* v_tail_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1885_; 
v_head_1875_ = lean_ctor_get(v_a_1872_, 0);
v_tail_1876_ = lean_ctor_get(v_a_1872_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_a_1872_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1878_ = v_a_1872_;
v_isShared_1879_ = v_isSharedCheck_1885_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_tail_1876_);
lean_inc(v_head_1875_);
lean_dec(v_a_1872_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1885_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1880_ = l_Lean_MessageData_ofSyntax(v_head_1875_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v_a_1873_);
lean_ctor_set(v___x_1878_, 0, v___x_1880_);
v___x_1882_ = v___x_1878_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_a_1873_);
v___x_1882_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
v_a_1872_ = v_tail_1876_;
v_a_1873_ = v___x_1882_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1));
v___x_1895_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3));
v___x_1896_ = l_Lean_Name_append(v___x_1895_, v___x_1894_);
return v___x_1896_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__5));
v___x_1899_ = l_Lean_stringToMessageData(v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds(lean_object* v_declName_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1908_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1));
v___x_1909_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36));
v___x_1910_ = 1;
lean_inc(v_declName_1900_);
v___x_1911_ = l_Lean_Elab_Deriving_mkContext(v___x_1908_, v___x_1909_, v_declName_1900_, v___x_1910_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc_n(v_a_1912_, 2);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs(v_a_1912_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = lean_unsigned_to_nat(1u);
v___x_1916_ = lean_mk_empty_array_with_capacity(v___x_1915_);
lean_inc_ref(v___x_1916_);
v___x_1917_ = lean_array_push(v___x_1916_, v_declName_1900_);
v___x_1918_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_1912_, v___x_1908_, v___x_1917_, v___x_1910_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec_ref(v___x_1917_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_toCold_1919_; lean_object* v_options_1920_; lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1961_; 
v_toCold_1919_ = lean_ctor_get(v_a_1905_, 0);
v_options_1920_ = lean_ctor_get(v_toCold_1919_, 2);
v_a_1921_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1923_ = v___x_1918_;
v_isShared_1924_ = v_isSharedCheck_1961_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1918_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1961_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v_inheritedTraceOptions_1925_; uint8_t v_hasTrace_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_inheritedTraceOptions_1925_ = lean_ctor_get(v_toCold_1919_, 11);
v_hasTrace_1926_ = lean_ctor_get_uint8(v_options_1920_, sizeof(void*)*1);
v___x_1927_ = lean_array_push(v___x_1916_, v_a_1914_);
v___x_1928_ = l_Array_append___redArg(v___x_1927_, v_a_1921_);
lean_dec(v_a_1921_);
if (v_hasTrace_1926_ == 0)
{
lean_object* v___x_1930_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1928_);
v___x_1930_ = v___x_1923_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1932_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1));
v___x_1933_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4_once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4);
v___x_1934_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1925_, v_options_1920_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1936_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1928_);
v___x_1936_ = v___x_1923_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1928_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_del_object(v___x_1923_);
v___x_1938_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6_once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6);
lean_inc_ref(v___x_1928_);
v___x_1939_ = lean_array_to_list(v___x_1928_);
v___x_1940_ = lean_box(0);
v___x_1941_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0(v___x_1939_, v___x_1940_);
v___x_1942_ = l_Lean_MessageData_ofList(v___x_1941_);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1938_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(v___x_1932_, v___x_1943_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v___x_1944_, 0);
lean_dec(v_unused_1952_);
v___x_1946_ = v___x_1944_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_dec(v___x_1944_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1928_);
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1928_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v___x_1928_);
v_a_1953_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1944_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1944_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v___x_1916_);
lean_dec(v_a_1914_);
v_a_1962_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1918_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1918_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec(v_a_1912_);
lean_dec(v_declName_1900_);
v_a_1970_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1913_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1913_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v_declName_1900_);
v_a_1978_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1911_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1911_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___boxed(lean_object* v_declName_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds(v_declName_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1(lean_object* v_cls_1995_, lean_object* v_msg_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(v_cls_1995_, v_msg_1996_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___boxed(lean_object* v_cls_2005_, lean_object* v_msg_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1(v_cls_2005_, v_msg_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(lean_object* v_declName_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; lean_object* v_env_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2018_ = lean_st_ref_get(v___y_2016_);
v_env_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc_ref(v_env_2019_);
lean_dec(v___x_2018_);
v___x_2020_ = l_Lean_isInductiveCore(v_env_2019_, v_declName_2015_);
v___x_2021_ = lean_box(v___x_2020_);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg___boxed(lean_object* v_declName_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(v_declName_2023_, v___y_2024_);
lean_dec(v___y_2024_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0(lean_object* v_declName_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(v_declName_2027_, v___y_2029_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___boxed(lean_object* v_declName_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0(v_declName_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0(uint8_t v_____do__lift_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
if (v_____do__lift_2037_ == 0)
{
uint8_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2041_ = 1;
v___x_2042_ = lean_box(v___x_2041_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
return v___x_2043_;
}
else
{
uint8_t v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = 0;
v___x_2045_ = lean_box(v___x_2044_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0___boxed(lean_object* v_____do__lift_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
uint8_t v_____do__lift_3600__boxed_2051_; lean_object* v_res_2052_; 
v_____do__lift_3600__boxed_2051_ = lean_unbox(v_____do__lift_2047_);
v_res_2052_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0(v_____do__lift_3600__boxed_2051_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(lean_object* v_as_2053_, size_t v_i_2054_, size_t v_stop_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
uint8_t v___x_2063_; 
v___x_2063_ = lean_usize_dec_eq(v_i_2054_, v_stop_2055_);
if (v___x_2063_ == 0)
{
uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = 1;
v___x_2065_ = lean_array_uget_borrowed(v_as_2053_, v_i_2054_);
lean_inc(v___x_2065_);
v___x_2066_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(v___x_2065_, v___y_2057_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2076_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2076_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2076_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_unbox(v_a_2067_);
lean_dec(v_a_2067_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = lean_box(v___x_2064_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2072_);
v___x_2074_ = v___x_2069_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
else
{
lean_del_object(v___x_2069_);
goto v___jp_2059_;
}
}
}
else
{
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2086_; 
v_a_2077_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2079_ = v___x_2066_;
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2066_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
uint8_t v___x_2081_; 
v___x_2081_ = lean_unbox(v_a_2077_);
lean_dec(v_a_2077_);
if (v___x_2081_ == 0)
{
lean_del_object(v___x_2079_);
goto v___jp_2059_;
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2082_ = lean_box(v___x_2064_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2082_);
v___x_2084_ = v___x_2079_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
return v___x_2066_;
}
}
}
else
{
uint8_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = 0;
v___x_2088_ = lean_box(v___x_2087_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
v___jp_2059_:
{
size_t v___x_2060_; size_t v___x_2061_; 
v___x_2060_ = ((size_t)1ULL);
v___x_2061_ = lean_usize_add(v_i_2054_, v___x_2060_);
v_i_2054_ = v___x_2061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3___boxed(lean_object* v_as_2090_, lean_object* v_i_2091_, lean_object* v_stop_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
size_t v_i_boxed_2096_; size_t v_stop_boxed_2097_; lean_object* v_res_2098_; 
v_i_boxed_2096_ = lean_unbox_usize(v_i_2091_);
lean_dec(v_i_2091_);
v_stop_boxed_2097_ = lean_unbox_usize(v_stop_2092_);
lean_dec(v_stop_2092_);
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(v_as_2090_, v_i_boxed_2096_, v_stop_boxed_2097_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec_ref(v_as_2090_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(lean_object* v_as_2099_, size_t v_i_2100_, size_t v_stop_2101_, lean_object* v_b_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
uint8_t v___x_2106_; 
v___x_2106_ = lean_usize_dec_eq(v_i_2100_, v_stop_2101_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_array_uget_borrowed(v_as_2099_, v_i_2100_);
lean_inc(v___x_2107_);
v___x_2108_ = l_Lean_Elab_Command_elabCommand(v___x_2107_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; size_t v___x_2110_; size_t v___x_2111_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v___x_2110_ = ((size_t)1ULL);
v___x_2111_ = lean_usize_add(v_i_2100_, v___x_2110_);
v_i_2100_ = v___x_2111_;
v_b_2102_ = v_a_2109_;
goto _start;
}
else
{
return v___x_2108_;
}
}
else
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v_b_2102_);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1___boxed(lean_object* v_as_2114_, lean_object* v_i_2115_, lean_object* v_stop_2116_, lean_object* v_b_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
size_t v_i_boxed_2121_; size_t v_stop_boxed_2122_; lean_object* v_res_2123_; 
v_i_boxed_2121_ = lean_unbox_usize(v_i_2115_);
lean_dec(v_i_2115_);
v_stop_boxed_2122_ = lean_unbox_usize(v_stop_2116_);
lean_dec(v_stop_2116_);
v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_as_2114_, v_i_boxed_2121_, v_stop_boxed_2122_, v_b_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec_ref(v_as_2114_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0(lean_object* v___x_2124_, lean_object* v___x_2125_, lean_object* v___x_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_2124_, v___y_2127_, v___y_2128_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2150_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2150_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2150_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = lean_array_get_size(v_a_2131_);
v___x_2136_ = lean_nat_dec_lt(v___x_2125_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2138_; 
lean_dec(v_a_2131_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2126_);
v___x_2138_ = v___x_2133_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2126_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
else
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_nat_dec_le(v___x_2135_, v___x_2135_);
if (v___x_2140_ == 0)
{
if (v___x_2136_ == 0)
{
lean_object* v___x_2142_; 
lean_dec(v_a_2131_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2126_);
v___x_2142_ = v___x_2133_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2126_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
else
{
size_t v___x_2144_; size_t v___x_2145_; lean_object* v___x_2146_; 
lean_del_object(v___x_2133_);
v___x_2144_ = ((size_t)0ULL);
v___x_2145_ = lean_usize_of_nat(v___x_2135_);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_a_2131_, v___x_2144_, v___x_2145_, v___x_2126_, v___y_2127_, v___y_2128_);
lean_dec(v_a_2131_);
return v___x_2146_;
}
}
else
{
size_t v___x_2147_; size_t v___x_2148_; lean_object* v___x_2149_; 
lean_del_object(v___x_2133_);
v___x_2147_ = ((size_t)0ULL);
v___x_2148_ = lean_usize_of_nat(v___x_2135_);
v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_a_2131_, v___x_2147_, v___x_2148_, v___x_2126_, v___y_2127_, v___y_2128_);
lean_dec(v_a_2131_);
return v___x_2149_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
v_a_2151_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2130_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2130_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0___boxed(lean_object* v___x_2159_, lean_object* v___x_2160_, lean_object* v___x_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0(v___x_2159_, v___x_2160_, v___x_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___x_2160_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(lean_object* v_as_2166_, size_t v_sz_2167_, size_t v_i_2168_, lean_object* v_b_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_usize_dec_lt(v_i_2168_, v_sz_2167_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v_b_2169_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v_a_2177_; lean_object* v___x_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_box(0);
v_a_2177_ = lean_array_uget_borrowed(v_as_2166_, v_i_2168_);
lean_inc_n(v_a_2177_, 2);
v___x_2178_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_2178_, 0, v_a_2177_);
v___f_2179_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2179_, 0, v___x_2178_);
lean_closure_set(v___f_2179_, 1, v___x_2175_);
lean_closure_set(v___f_2179_, 2, v___x_2176_);
v___x_2180_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_2177_, v___f_2179_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2180_) == 0)
{
size_t v___x_2181_; size_t v___x_2182_; 
lean_dec_ref_known(v___x_2180_, 1);
v___x_2181_ = ((size_t)1ULL);
v___x_2182_ = lean_usize_add(v_i_2168_, v___x_2181_);
v_i_2168_ = v___x_2182_;
v_b_2169_ = v___x_2176_;
goto _start;
}
else
{
return v___x_2180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___boxed(lean_object* v_as_2184_, lean_object* v_sz_2185_, lean_object* v_i_2186_, lean_object* v_b_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
size_t v_sz_boxed_2191_; size_t v_i_boxed_2192_; lean_object* v_res_2193_; 
v_sz_boxed_2191_ = lean_unbox_usize(v_sz_2185_);
lean_dec(v_sz_2185_);
v_i_boxed_2192_ = lean_unbox_usize(v_i_2186_);
lean_dec(v_i_2186_);
v_res_2193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(v_as_2184_, v_sz_boxed_2191_, v_i_boxed_2192_, v_b_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec_ref(v_as_2184_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1(lean_object* v_declNames_2194_, lean_object* v___x_2195_, lean_object* v___x_2196_, lean_object* v___f_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___y_2225_; uint8_t v___x_2228_; 
v___x_2228_ = lean_nat_dec_lt(v___x_2195_, v___x_2196_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_box(v___x_2228_);
lean_inc(v___y_2199_);
lean_inc_ref(v___y_2198_);
v___x_2230_ = lean_apply_4(v___f_2197_, v___x_2229_, v___y_2198_, v___y_2199_, lean_box(0));
v___y_2225_ = v___x_2230_;
goto v___jp_2224_;
}
else
{
if (v___x_2228_ == 0)
{
lean_dec_ref(v___f_2197_);
goto v___jp_2201_;
}
else
{
size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = ((size_t)0ULL);
v___x_2232_ = lean_usize_of_nat(v___x_2196_);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(v_declNames_2194_, v___x_2231_, v___x_2232_, v___y_2198_, v___y_2199_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
lean_inc(v___y_2199_);
lean_inc_ref(v___y_2198_);
v___x_2235_ = lean_apply_4(v___f_2197_, v_a_2234_, v___y_2198_, v___y_2199_, lean_box(0));
v___y_2225_ = v___x_2235_;
goto v___jp_2224_;
}
else
{
lean_dec_ref(v___f_2197_);
v___y_2225_ = v___x_2233_;
goto v___jp_2224_;
}
}
}
v___jp_2201_:
{
lean_object* v___x_2202_; size_t v_sz_2203_; size_t v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = lean_box(0);
v_sz_2203_ = lean_array_size(v_declNames_2194_);
v___x_2204_ = ((size_t)0ULL);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(v_declNames_2194_, v_sz_2203_, v___x_2204_, v___x_2202_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2214_; 
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v___x_2205_, 0);
lean_dec(v_unused_2215_);
v___x_2207_ = v___x_2205_;
v_isShared_2208_ = v_isSharedCheck_2214_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v___x_2205_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2214_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2209_ = 1;
v___x_2210_ = lean_box(v___x_2209_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2210_);
v___x_2212_ = v___x_2207_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
v_a_2216_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2205_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2205_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
v___jp_2224_:
{
if (lean_obj_tag(v___y_2225_) == 0)
{
lean_object* v_a_2226_; uint8_t v___x_2227_; 
v_a_2226_ = lean_ctor_get(v___y_2225_, 0);
v___x_2227_ = lean_unbox(v_a_2226_);
if (v___x_2227_ == 0)
{
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
return v___y_2225_;
}
else
{
lean_dec_ref_known(v___y_2225_, 1);
goto v___jp_2201_;
}
}
else
{
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
return v___y_2225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1___boxed(lean_object* v_declNames_2236_, lean_object* v___x_2237_, lean_object* v___x_2238_, lean_object* v___f_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1(v_declNames_2236_, v___x_2237_, v___x_2238_, v___f_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___x_2238_);
lean_dec(v___x_2237_);
lean_dec_ref(v_declNames_2236_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(lean_object* v___y_2244_, uint8_t v_isExporting_2245_, lean_object* v_a_x3f_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v_env_2249_; lean_object* v_messages_2250_; lean_object* v_scopes_2251_; lean_object* v_usedQuotCtxts_2252_; lean_object* v_nextMacroScope_2253_; lean_object* v_maxRecDepth_2254_; lean_object* v_ngen_2255_; lean_object* v_auxDeclNGen_2256_; lean_object* v_infoState_2257_; lean_object* v_traceState_2258_; lean_object* v_snapshotTasks_2259_; lean_object* v_prevLinterStates_2260_; lean_object* v_codeQualityEntryTasks_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2272_; 
v___x_2248_ = lean_st_ref_take(v___y_2244_);
v_env_2249_ = lean_ctor_get(v___x_2248_, 0);
v_messages_2250_ = lean_ctor_get(v___x_2248_, 1);
v_scopes_2251_ = lean_ctor_get(v___x_2248_, 2);
v_usedQuotCtxts_2252_ = lean_ctor_get(v___x_2248_, 3);
v_nextMacroScope_2253_ = lean_ctor_get(v___x_2248_, 4);
v_maxRecDepth_2254_ = lean_ctor_get(v___x_2248_, 5);
v_ngen_2255_ = lean_ctor_get(v___x_2248_, 6);
v_auxDeclNGen_2256_ = lean_ctor_get(v___x_2248_, 7);
v_infoState_2257_ = lean_ctor_get(v___x_2248_, 8);
v_traceState_2258_ = lean_ctor_get(v___x_2248_, 9);
v_snapshotTasks_2259_ = lean_ctor_get(v___x_2248_, 10);
v_prevLinterStates_2260_ = lean_ctor_get(v___x_2248_, 11);
v_codeQualityEntryTasks_2261_ = lean_ctor_get(v___x_2248_, 12);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2263_ = v___x_2248_;
v_isShared_2264_ = v_isSharedCheck_2272_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2261_);
lean_inc(v_prevLinterStates_2260_);
lean_inc(v_snapshotTasks_2259_);
lean_inc(v_traceState_2258_);
lean_inc(v_infoState_2257_);
lean_inc(v_auxDeclNGen_2256_);
lean_inc(v_ngen_2255_);
lean_inc(v_maxRecDepth_2254_);
lean_inc(v_nextMacroScope_2253_);
lean_inc(v_usedQuotCtxts_2252_);
lean_inc(v_scopes_2251_);
lean_inc(v_messages_2250_);
lean_inc(v_env_2249_);
lean_dec(v___x_2248_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2272_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2265_ = l_Lean_Environment_setExporting(v_env_2249_, v_isExporting_2245_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2265_);
v___x_2267_ = v___x_2263_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_messages_2250_);
lean_ctor_set(v_reuseFailAlloc_2271_, 2, v_scopes_2251_);
lean_ctor_set(v_reuseFailAlloc_2271_, 3, v_usedQuotCtxts_2252_);
lean_ctor_set(v_reuseFailAlloc_2271_, 4, v_nextMacroScope_2253_);
lean_ctor_set(v_reuseFailAlloc_2271_, 5, v_maxRecDepth_2254_);
lean_ctor_set(v_reuseFailAlloc_2271_, 6, v_ngen_2255_);
lean_ctor_set(v_reuseFailAlloc_2271_, 7, v_auxDeclNGen_2256_);
lean_ctor_set(v_reuseFailAlloc_2271_, 8, v_infoState_2257_);
lean_ctor_set(v_reuseFailAlloc_2271_, 9, v_traceState_2258_);
lean_ctor_set(v_reuseFailAlloc_2271_, 10, v_snapshotTasks_2259_);
lean_ctor_set(v_reuseFailAlloc_2271_, 11, v_prevLinterStates_2260_);
lean_ctor_set(v_reuseFailAlloc_2271_, 12, v_codeQualityEntryTasks_2261_);
v___x_2267_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = lean_st_ref_put(v___y_2244_, v___x_2267_);
v___x_2269_ = lean_box(0);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v___y_2273_, lean_object* v_isExporting_2274_, lean_object* v_a_x3f_2275_, lean_object* v___y_2276_){
_start:
{
uint8_t v_isExporting_boxed_2277_; lean_object* v_res_2278_; 
v_isExporting_boxed_2277_ = lean_unbox(v_isExporting_2274_);
v_res_2278_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_2273_, v_isExporting_boxed_2277_, v_a_x3f_2275_);
lean_dec(v_a_x3f_2275_);
lean_dec(v___y_2273_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(lean_object* v_x_2279_, uint8_t v_isExporting_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v_env_2285_; lean_object* v___x_2286_; uint8_t v_isModule_2287_; 
v___x_2284_ = lean_st_ref_get(v___y_2282_);
v_env_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc_ref(v_env_2285_);
lean_dec(v___x_2284_);
v___x_2286_ = l_Lean_Environment_header(v_env_2285_);
v_isModule_2287_ = lean_ctor_get_uint8(v___x_2286_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2286_);
if (v_isModule_2287_ == 0)
{
lean_object* v___x_2288_; 
lean_dec_ref(v_env_2285_);
lean_inc(v___y_2282_);
lean_inc_ref(v___y_2281_);
v___x_2288_ = lean_apply_3(v_x_2279_, v___y_2281_, v___y_2282_, lean_box(0));
return v___x_2288_;
}
else
{
uint8_t v_isExporting_2289_; 
v_isExporting_2289_ = lean_ctor_get_uint8(v_env_2285_, sizeof(void*)*8);
lean_dec_ref(v_env_2285_);
if (v_isExporting_2280_ == 0)
{
if (v_isExporting_2289_ == 0)
{
lean_object* v___x_2343_; 
lean_inc(v___y_2282_);
lean_inc_ref(v___y_2281_);
v___x_2343_ = lean_apply_3(v_x_2279_, v___y_2281_, v___y_2282_, lean_box(0));
return v___x_2343_;
}
else
{
goto v___jp_2290_;
}
}
else
{
if (v_isExporting_2289_ == 0)
{
goto v___jp_2290_;
}
else
{
lean_object* v___x_2344_; 
lean_inc(v___y_2282_);
lean_inc_ref(v___y_2281_);
v___x_2344_ = lean_apply_3(v_x_2279_, v___y_2281_, v___y_2282_, lean_box(0));
return v___x_2344_;
}
}
v___jp_2290_:
{
lean_object* v___x_2291_; lean_object* v_env_2292_; lean_object* v_messages_2293_; lean_object* v_scopes_2294_; lean_object* v_usedQuotCtxts_2295_; lean_object* v_nextMacroScope_2296_; lean_object* v_maxRecDepth_2297_; lean_object* v_ngen_2298_; lean_object* v_auxDeclNGen_2299_; lean_object* v_infoState_2300_; lean_object* v_traceState_2301_; lean_object* v_snapshotTasks_2302_; lean_object* v_prevLinterStates_2303_; lean_object* v_codeQualityEntryTasks_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2342_; 
v___x_2291_ = lean_st_ref_take(v___y_2282_);
v_env_2292_ = lean_ctor_get(v___x_2291_, 0);
v_messages_2293_ = lean_ctor_get(v___x_2291_, 1);
v_scopes_2294_ = lean_ctor_get(v___x_2291_, 2);
v_usedQuotCtxts_2295_ = lean_ctor_get(v___x_2291_, 3);
v_nextMacroScope_2296_ = lean_ctor_get(v___x_2291_, 4);
v_maxRecDepth_2297_ = lean_ctor_get(v___x_2291_, 5);
v_ngen_2298_ = lean_ctor_get(v___x_2291_, 6);
v_auxDeclNGen_2299_ = lean_ctor_get(v___x_2291_, 7);
v_infoState_2300_ = lean_ctor_get(v___x_2291_, 8);
v_traceState_2301_ = lean_ctor_get(v___x_2291_, 9);
v_snapshotTasks_2302_ = lean_ctor_get(v___x_2291_, 10);
v_prevLinterStates_2303_ = lean_ctor_get(v___x_2291_, 11);
v_codeQualityEntryTasks_2304_ = lean_ctor_get(v___x_2291_, 12);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2306_ = v___x_2291_;
v_isShared_2307_ = v_isSharedCheck_2342_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2304_);
lean_inc(v_prevLinterStates_2303_);
lean_inc(v_snapshotTasks_2302_);
lean_inc(v_traceState_2301_);
lean_inc(v_infoState_2300_);
lean_inc(v_auxDeclNGen_2299_);
lean_inc(v_ngen_2298_);
lean_inc(v_maxRecDepth_2297_);
lean_inc(v_nextMacroScope_2296_);
lean_inc(v_usedQuotCtxts_2295_);
lean_inc(v_scopes_2294_);
lean_inc(v_messages_2293_);
lean_inc(v_env_2292_);
lean_dec(v___x_2291_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2342_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2310_; 
v___x_2308_ = l_Lean_Environment_setExporting(v_env_2292_, v_isExporting_2280_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2308_);
v___x_2310_ = v___x_2306_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_messages_2293_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_scopes_2294_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_usedQuotCtxts_2295_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v_nextMacroScope_2296_);
lean_ctor_set(v_reuseFailAlloc_2341_, 5, v_maxRecDepth_2297_);
lean_ctor_set(v_reuseFailAlloc_2341_, 6, v_ngen_2298_);
lean_ctor_set(v_reuseFailAlloc_2341_, 7, v_auxDeclNGen_2299_);
lean_ctor_set(v_reuseFailAlloc_2341_, 8, v_infoState_2300_);
lean_ctor_set(v_reuseFailAlloc_2341_, 9, v_traceState_2301_);
lean_ctor_set(v_reuseFailAlloc_2341_, 10, v_snapshotTasks_2302_);
lean_ctor_set(v_reuseFailAlloc_2341_, 11, v_prevLinterStates_2303_);
lean_ctor_set(v_reuseFailAlloc_2341_, 12, v_codeQualityEntryTasks_2304_);
v___x_2310_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; lean_object* v_r_2312_; 
v___x_2311_ = lean_st_ref_put(v___y_2282_, v___x_2310_);
lean_inc(v___y_2282_);
lean_inc_ref(v___y_2281_);
v_r_2312_ = lean_apply_3(v_x_2279_, v___y_2281_, v___y_2282_, lean_box(0));
if (lean_obj_tag(v_r_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2329_; 
v_a_2313_ = lean_ctor_get(v_r_2312_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_r_2312_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2315_ = v_r_2312_;
v_isShared_2316_ = v_isSharedCheck_2329_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v_r_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2329_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
lean_inc(v_a_2313_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set_tag(v___x_2315_, 1);
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
v___x_2319_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_2282_, v_isExporting_2289_, v___x_2318_);
lean_dec_ref(v___x_2318_);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; 
v_unused_2327_ = lean_ctor_get(v___x_2319_, 0);
lean_dec(v_unused_2327_);
v___x_2321_ = v___x_2319_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_dec(v___x_2319_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v_a_2313_);
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2313_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
v_a_2330_ = lean_ctor_get(v_r_2312_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v_r_2312_, 1);
v___x_2331_ = lean_box(0);
v___x_2332_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_2282_, v_isExporting_2289_, v___x_2331_);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v___x_2332_, 0);
lean_dec(v_unused_2340_);
v___x_2334_ = v___x_2332_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_dec(v___x_2332_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
lean_ctor_set_tag(v___x_2334_, 1);
lean_ctor_set(v___x_2334_, 0, v_a_2330_);
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2330_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___boxed(lean_object* v_x_2345_, lean_object* v_isExporting_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
uint8_t v_isExporting_boxed_2350_; lean_object* v_res_2351_; 
v_isExporting_boxed_2350_ = lean_unbox(v_isExporting_2346_);
v_res_2351_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_2345_, v_isExporting_boxed_2350_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(lean_object* v_x_2352_, uint8_t v_when_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
if (v_when_2353_ == 0)
{
lean_object* v___x_2357_; 
lean_inc(v___y_2355_);
lean_inc_ref(v___y_2354_);
v___x_2357_ = lean_apply_3(v_x_2352_, v___y_2354_, v___y_2355_, lean_box(0));
return v___x_2357_;
}
else
{
uint8_t v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = 0;
v___x_2359_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_2352_, v___x_2358_, v___y_2354_, v___y_2355_);
return v___x_2359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg___boxed(lean_object* v_x_2360_, lean_object* v_when_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v_when_boxed_2365_; lean_object* v_res_2366_; 
v_when_boxed_2365_ = lean_unbox(v_when_2361_);
v_res_2366_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v_x_2360_, v_when_boxed_2365_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler(lean_object* v_declNames_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___f_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___f_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; 
v___f_2372_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHandler___closed__0));
v___x_2373_ = lean_unsigned_to_nat(0u);
v___x_2374_ = lean_array_get_size(v_declNames_2368_);
v___f_2375_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1___boxed), 7, 4);
lean_closure_set(v___f_2375_, 0, v_declNames_2368_);
lean_closure_set(v___f_2375_, 1, v___x_2373_);
lean_closure_set(v___f_2375_, 2, v___x_2374_);
lean_closure_set(v___f_2375_, 3, v___f_2372_);
v___x_2376_ = 1;
v___x_2377_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v___f_2375_, v___x_2376_, v_a_2369_, v_a_2370_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___boxed(lean_object* v_declNames_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler(v_declNames_2378_, v_a_2379_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4(lean_object* v_00_u03b1_2383_, lean_object* v_x_2384_, uint8_t v_isExporting_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_2384_, v_isExporting_2385_, v___y_2386_, v___y_2387_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2390_, lean_object* v_x_2391_, lean_object* v_isExporting_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
uint8_t v_isExporting_boxed_2396_; lean_object* v_res_2397_; 
v_isExporting_boxed_2396_ = lean_unbox(v_isExporting_2392_);
v_res_2397_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4(v_00_u03b1_2390_, v_x_2391_, v_isExporting_boxed_2396_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4(lean_object* v_00_u03b1_2398_, lean_object* v_x_2399_, uint8_t v_when_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v_x_2399_, v_when_2400_, v___y_2401_, v___y_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___boxed(lean_object* v_00_u03b1_2405_, lean_object* v_x_2406_, lean_object* v_when_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
uint8_t v_when_boxed_2411_; lean_object* v_res_2412_; 
v_when_boxed_2411_ = lean_unbox(v_when_2407_);
v_res_2412_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4(v_00_u03b1_2405_, v_x_2406_, v_when_boxed_2411_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
return v_res_2412_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_unsigned_to_nat(4079464183u);
v___x_2466_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__19_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2467_ = l_Lean_Name_num___override(v___x_2466_, v___x_2465_);
return v___x_2467_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__21_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2470_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2471_ = l_Lean_Name_str___override(v___x_2470_, v___x_2469_);
return v___x_2471_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__23_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2474_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2475_ = l_Lean_Name_str___override(v___x_2474_, v___x_2473_);
return v___x_2475_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_unsigned_to_nat(2u);
v___x_2477_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2478_ = l_Lean_Name_num___override(v___x_2477_, v___x_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1));
v___x_2481_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__0_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2482_ = l_Lean_Elab_registerDerivingHandler(v___x_2480_, v___x_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v___x_2483_; uint8_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref_known(v___x_2482_, 1);
v___x_2483_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1));
v___x_2484_ = 0;
v___x_2485_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2486_ = l_Lean_registerTraceClass(v___x_2483_, v___x_2484_, v___x_2485_);
return v___x_2486_;
}
else
{
return v___x_2482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2____boxed(lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_();
return v_res_2488_;
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
