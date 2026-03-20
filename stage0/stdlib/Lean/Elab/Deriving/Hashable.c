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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mixHash"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__7_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(189, 74, 20, 35, 61, 24, 14, 25)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__11_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__12_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__13_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__14_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__16_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__18_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__19_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__20_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__21_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__23 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__23_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__24_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__25_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__25_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 149, 214, 102, 1, 219, 34, 253)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__25_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__25_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__26_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__27_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__28_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__27_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__28_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__28_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__29_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__30_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__30_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__30_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__30_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__31_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__33_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__33_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__33 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__33_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__33_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__34_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__35 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__35_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__31_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__35_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__36_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__29_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__36_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__37_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__26_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__37_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__38_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hash"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__39_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__40;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__39_value),LEAN_SCALAR_PTR_LITERAL(191, 103, 194, 67, 121, 216, 187, 106)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__41_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 184, 111, 151, 29, 127, 247, 194)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__42_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__39_value),LEAN_SCALAR_PTR_LITERAL(241, 83, 211, 250, 180, 43, 84, 158)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__42_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__42_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__43 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__43_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__43_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__44 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__44_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__45 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__45_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__2_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__2_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__5_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__6_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__7_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__8;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___boxed(lean_object**);
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
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___closed__0_value;
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__11_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
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
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__18_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__25 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30_value)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__31_value),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33_value)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44_value)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "hashable"};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 166, 247, 31, 207, 69, 133, 232)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__2_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 225, 45, 251, 162, 86, 82, 173)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(73, 154, 190, 192, 211, 16, 57, 209)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(140, 19, 134, 125, 143, 124, 44, 190)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(70, 22, 76, 54, 190, 199, 213, 91)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__10_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(108, 133, 113, 226, 183, 145, 134, 17)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__15_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(127, 168, 84, 49, 33, 100, 57, 131)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(33, 135, 77, 5, 241, 59, 88, 154)}};
static const lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__18_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(119, 51, 149, 107, 14, 108, 122, 130)}};
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
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___lam__0(lean_object* v_k_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v_b_27_, lean_object* v_c_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_apply_9(v_k_24_, v_b_27_, v_c_28_, v___y_25_, v___y_26_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, lean_box(0));
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___lam__0___boxed(lean_object* v_k_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v_b_38_, lean_object* v_c_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___lam__0(v_k_35_, v___y_36_, v___y_37_, v_b_38_, v_c_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(lean_object* v_type_46_, lean_object* v_k_47_, uint8_t v_cleanupAnnotations_48_, uint8_t v_whnfType_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___f_57_; lean_object* v___x_58_; 
v___f_57_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___lam__0___boxed), 10, 3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___boxed(lean_object* v_type_67_, lean_object* v_k_68_, lean_object* v_cleanupAnnotations_69_, lean_object* v_whnfType_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_78_; uint8_t v_whnfType_boxed_79_; lean_object* v_res_80_; 
v_cleanupAnnotations_boxed_78_ = lean_unbox(v_cleanupAnnotations_69_);
v_whnfType_boxed_79_ = lean_unbox(v_whnfType_70_);
v_res_80_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_type_67_, v_k_68_, v_cleanupAnnotations_boxed_78_, v_whnfType_boxed_79_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4(lean_object* v_00_u03b1_81_, lean_object* v_type_82_, lean_object* v_k_83_, uint8_t v_cleanupAnnotations_84_, uint8_t v_whnfType_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_type_82_, v_k_83_, v_cleanupAnnotations_84_, v_whnfType_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___boxed(lean_object* v_00_u03b1_94_, lean_object* v_type_95_, lean_object* v_k_96_, lean_object* v_cleanupAnnotations_97_, lean_object* v_whnfType_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_106_; uint8_t v_whnfType_boxed_107_; lean_object* v_res_108_; 
v_cleanupAnnotations_boxed_106_ = lean_unbox(v_cleanupAnnotations_97_);
v_whnfType_boxed_107_ = lean_unbox(v_whnfType_98_);
v_res_108_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4(v_00_u03b1_94_, v_type_95_, v_k_96_, v_cleanupAnnotations_boxed_106_, v_whnfType_boxed_107_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(size_t v_sz_109_, size_t v_i_110_, lean_object* v_bs_111_){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = lean_usize_dec_lt(v_i_110_, v_sz_109_);
if (v___x_112_ == 0)
{
return v_bs_111_;
}
else
{
lean_object* v_v_113_; lean_object* v___x_114_; lean_object* v_bs_x27_115_; size_t v___x_116_; size_t v___x_117_; lean_object* v___x_118_; 
v_v_113_ = lean_array_uget(v_bs_111_, v_i_110_);
v___x_114_ = lean_unsigned_to_nat(0u);
v_bs_x27_115_ = lean_array_uset(v_bs_111_, v_i_110_, v___x_114_);
v___x_116_ = ((size_t)1ULL);
v___x_117_ = lean_usize_add(v_i_110_, v___x_116_);
v___x_118_ = lean_array_uset(v_bs_x27_115_, v_i_110_, v_v_113_);
v_i_110_ = v___x_117_;
v_bs_111_ = v___x_118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___boxed(lean_object* v_sz_120_, lean_object* v_i_121_, lean_object* v_bs_122_){
_start:
{
size_t v_sz_boxed_123_; size_t v_i_boxed_124_; lean_object* v_res_125_; 
v_sz_boxed_123_ = lean_unbox_usize(v_sz_120_);
lean_dec(v_sz_120_);
v_i_boxed_124_ = lean_unbox_usize(v_i_121_);
lean_dec(v_i_121_);
v_res_125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(v_sz_boxed_123_, v_i_boxed_124_, v_bs_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0(lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_ref_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_ref_133_ = lean_ctor_get(v___y_130_, 5);
v___x_134_ = 0;
v___x_135_ = l_Lean_SourceInfo_fromRef(v_ref_133_, v___x_134_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0___boxed(lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0(v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
return v_res_144_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__1(lean_object* v_declName_145_, lean_object* v_x_146_){
_start:
{
uint8_t v___x_147_; 
v___x_147_ = lean_name_eq(v_x_146_, v_declName_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__1___boxed(lean_object* v_declName_148_, lean_object* v_x_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__1(v_declName_148_, v_x_149_);
lean_dec(v_x_149_);
lean_dec(v_declName_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__0(lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_ref_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_ref_159_ = lean_ctor_get(v___y_156_, 5);
v___x_160_ = 0;
v___x_161_ = l_Lean_SourceInfo_fromRef(v_ref_159_, v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__0___boxed(lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__0(v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_170_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__7));
v___x_185_ = l_String_toRawSubstring_x27(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__21));
v___x_215_ = l_String_toRawSubstring_x27(v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__40(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__39));
v___x_258_ = l_String_toRawSubstring_x27(v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg(lean_object* v_upperBound_271_, lean_object* v___x_272_, lean_object* v_xs_273_, lean_object* v_allIndVals_274_, lean_object* v_ctx_275_, lean_object* v_a_276_, lean_object* v_b_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_a_286_; uint8_t v___x_290_; 
v___x_290_ = lean_nat_dec_lt(v_a_276_, v_upperBound_271_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v_a_276_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v_b_277_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__1));
lean_inc(v___y_283_);
lean_inc_ref(v___y_282_);
v___x_293_ = l_Lean_Core_mkFreshUserName(v___x_292_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref(v___x_293_);
v___x_295_ = l_Lean_instInhabitedExpr;
v___x_296_ = lean_nat_add(v___x_272_, v_a_276_);
v___x_297_ = lean_array_get_borrowed(v___x_295_, v_xs_273_, v___x_296_);
lean_dec(v___x_296_);
lean_inc(v___y_283_);
lean_inc_ref(v___y_282_);
lean_inc(v___y_281_);
lean_inc_ref(v___y_280_);
lean_inc(v___x_297_);
v___x_298_ = lean_infer_type(v___x_297_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_300_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_299_);
lean_dec_ref(v___x_298_);
lean_inc(v___y_283_);
lean_inc_ref(v___y_282_);
lean_inc(v___y_281_);
lean_inc_ref(v___y_280_);
v___x_300_ = lean_whnf(v_a_299_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v_fst_302_; lean_object* v_snd_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_451_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref(v___x_300_);
v_fst_302_ = lean_ctor_get(v_b_277_, 0);
v_snd_303_ = lean_ctor_get(v_b_277_, 1);
v_isSharedCheck_451_ = !lean_is_exclusive(v_b_277_);
if (v_isSharedCheck_451_ == 0)
{
v___x_305_ = v_b_277_;
v_isShared_306_ = v_isSharedCheck_451_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_snd_303_);
lean_inc(v_fst_302_);
lean_dec(v_b_277_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_451_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_mk_syntax_ident(v_a_294_);
lean_inc(v___x_307_);
v___x_308_ = lean_array_push(v_fst_302_, v___x_307_);
v___x_309_ = l_Lean_Expr_getAppFn(v_a_301_);
lean_dec(v_a_301_);
if (lean_obj_tag(v___x_309_) == 4)
{
lean_object* v_declName_310_; lean_object* v___f_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_declName_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_declName_310_);
lean_dec_ref(v___x_309_);
v___f_311_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_311_, 0, v_declName_310_);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = l_Array_findIdx_x3f_loop___redArg(v___f_311_, v_allIndVals_274_, v___x_312_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v___x_314_; 
v___x_314_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__0(v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v_quotContext_316_; lean_object* v_currMacroScope_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref(v___x_314_);
v_quotContext_316_ = lean_ctor_get(v___y_282_, 10);
v_currMacroScope_317_ = lean_ctor_get(v___y_282_, 11);
v___x_318_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6));
v___x_319_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8);
v___x_320_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__9));
lean_inc(v_currMacroScope_317_);
lean_inc(v_quotContext_316_);
v___x_321_ = l_Lean_addMacroScope(v_quotContext_316_, v___x_320_, v_currMacroScope_317_);
v___x_322_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__11));
lean_inc(v_a_315_);
v___x_323_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_323_, 0, v_a_315_);
lean_ctor_set(v___x_323_, 1, v___x_319_);
lean_ctor_set(v___x_323_, 2, v___x_321_);
lean_ctor_set(v___x_323_, 3, v___x_322_);
v___x_324_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__13));
v___x_325_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15));
v___x_326_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17));
v___x_327_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__18));
lean_inc(v_a_315_);
v___x_328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_328_, 0, v_a_315_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__20));
v___x_330_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22);
v___x_331_ = lean_box(0);
lean_inc(v_currMacroScope_317_);
lean_inc(v_quotContext_316_);
v___x_332_ = l_Lean_addMacroScope(v_quotContext_316_, v___x_331_, v_currMacroScope_317_);
v___x_333_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__38));
lean_inc(v_a_315_);
v___x_334_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_334_, 0, v_a_315_);
lean_ctor_set(v___x_334_, 1, v___x_330_);
lean_ctor_set(v___x_334_, 2, v___x_332_);
lean_ctor_set(v___x_334_, 3, v___x_333_);
lean_inc(v_a_315_);
v___x_335_ = l_Lean_Syntax_node1(v_a_315_, v___x_329_, v___x_334_);
lean_inc(v_a_315_);
v___x_336_ = l_Lean_Syntax_node2(v_a_315_, v___x_326_, v___x_328_, v___x_335_);
v___x_337_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__40);
v___x_338_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__41));
lean_inc(v_currMacroScope_317_);
lean_inc(v_quotContext_316_);
v___x_339_ = l_Lean_addMacroScope(v_quotContext_316_, v___x_338_, v_currMacroScope_317_);
v___x_340_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__44));
lean_inc(v_a_315_);
v___x_341_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_341_, 0, v_a_315_);
lean_ctor_set(v___x_341_, 1, v___x_337_);
lean_ctor_set(v___x_341_, 2, v___x_339_);
lean_ctor_set(v___x_341_, 3, v___x_340_);
lean_inc(v_a_315_);
v___x_342_ = l_Lean_Syntax_node1(v_a_315_, v___x_324_, v___x_307_);
lean_inc(v_a_315_);
v___x_343_ = l_Lean_Syntax_node2(v_a_315_, v___x_318_, v___x_341_, v___x_342_);
v___x_344_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__45));
lean_inc(v_a_315_);
v___x_345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_345_, 0, v_a_315_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
lean_inc(v_a_315_);
v___x_346_ = l_Lean_Syntax_node3(v_a_315_, v___x_325_, v___x_336_, v___x_343_, v___x_345_);
lean_inc(v_a_315_);
v___x_347_ = l_Lean_Syntax_node2(v_a_315_, v___x_324_, v_snd_303_, v___x_346_);
v___x_348_ = l_Lean_Syntax_node2(v_a_315_, v___x_318_, v___x_323_, v___x_347_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_348_);
lean_ctor_set(v___x_305_, 0, v___x_308_);
v___x_350_ = v___x_305_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
v_a_286_ = v___x_350_;
goto v___jp_285_;
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v___x_308_);
lean_dec(v___x_307_);
lean_del_object(v___x_305_);
lean_dec(v_snd_303_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v_a_276_);
v_a_352_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_314_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_314_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v_val_360_; lean_object* v___x_361_; 
v_val_360_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_val_360_);
lean_dec_ref(v___x_313_);
v___x_361_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__0(v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v_quotContext_363_; lean_object* v_currMacroScope_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_auxFunNames_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref(v___x_361_);
v_quotContext_363_ = lean_ctor_get(v___y_282_, 10);
v_currMacroScope_364_ = lean_ctor_get(v___y_282_, 11);
v___x_365_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6));
v___x_366_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8);
v___x_367_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__9));
lean_inc(v_currMacroScope_364_);
lean_inc(v_quotContext_363_);
v___x_368_ = l_Lean_addMacroScope(v_quotContext_363_, v___x_367_, v_currMacroScope_364_);
v___x_369_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__11));
lean_inc(v_a_362_);
v___x_370_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_370_, 0, v_a_362_);
lean_ctor_set(v___x_370_, 1, v___x_366_);
lean_ctor_set(v___x_370_, 2, v___x_368_);
lean_ctor_set(v___x_370_, 3, v___x_369_);
v___x_371_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15));
v___x_372_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17));
v___x_373_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__18));
lean_inc(v_a_362_);
v___x_374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_374_, 0, v_a_362_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22);
v___x_376_ = lean_box(0);
lean_inc(v_currMacroScope_364_);
lean_inc(v_quotContext_363_);
v___x_377_ = l_Lean_addMacroScope(v_quotContext_363_, v___x_376_, v_currMacroScope_364_);
v___x_378_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__38));
lean_inc(v_a_362_);
v___x_379_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_379_, 0, v_a_362_);
lean_ctor_set(v___x_379_, 1, v___x_375_);
lean_ctor_set(v___x_379_, 2, v___x_377_);
lean_ctor_set(v___x_379_, 3, v___x_378_);
v_auxFunNames_380_ = lean_ctor_get(v_ctx_275_, 2);
v___x_381_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__20));
lean_inc(v_a_362_);
v___x_382_ = l_Lean_Syntax_node1(v_a_362_, v___x_381_, v___x_379_);
v___x_383_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__13));
lean_inc(v_a_362_);
v___x_384_ = l_Lean_Syntax_node2(v_a_362_, v___x_372_, v___x_374_, v___x_382_);
v___x_385_ = lean_array_get_borrowed(v___x_376_, v_auxFunNames_380_, v_val_360_);
lean_dec(v_val_360_);
lean_inc(v___x_385_);
v___x_386_ = lean_mk_syntax_ident(v___x_385_);
lean_inc(v_a_362_);
v___x_387_ = l_Lean_Syntax_node1(v_a_362_, v___x_383_, v___x_307_);
lean_inc(v_a_362_);
v___x_388_ = l_Lean_Syntax_node2(v_a_362_, v___x_365_, v___x_386_, v___x_387_);
v___x_389_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__45));
lean_inc(v_a_362_);
v___x_390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_390_, 0, v_a_362_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
lean_inc(v_a_362_);
v___x_391_ = l_Lean_Syntax_node3(v_a_362_, v___x_371_, v___x_384_, v___x_388_, v___x_390_);
lean_inc(v_a_362_);
v___x_392_ = l_Lean_Syntax_node2(v_a_362_, v___x_383_, v_snd_303_, v___x_391_);
v___x_393_ = l_Lean_Syntax_node2(v_a_362_, v___x_365_, v___x_370_, v___x_392_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_393_);
lean_ctor_set(v___x_305_, 0, v___x_308_);
v___x_395_ = v___x_305_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
v_a_286_ = v___x_395_;
goto v___jp_285_;
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_val_360_);
lean_dec_ref(v___x_308_);
lean_dec(v___x_307_);
lean_del_object(v___x_305_);
lean_dec(v_snd_303_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v_a_276_);
v_a_397_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_361_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_361_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
else
{
lean_object* v___x_405_; 
lean_dec_ref(v___x_309_);
v___x_405_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___lam__0(v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v_quotContext_407_; lean_object* v_currMacroScope_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v___x_405_);
v_quotContext_407_ = lean_ctor_get(v___y_282_, 10);
v_currMacroScope_408_ = lean_ctor_get(v___y_282_, 11);
v___x_409_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6));
v___x_410_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__8);
v___x_411_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__9));
lean_inc(v_currMacroScope_408_);
lean_inc(v_quotContext_407_);
v___x_412_ = l_Lean_addMacroScope(v_quotContext_407_, v___x_411_, v_currMacroScope_408_);
v___x_413_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__11));
lean_inc(v_a_406_);
v___x_414_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_414_, 0, v_a_406_);
lean_ctor_set(v___x_414_, 1, v___x_410_);
lean_ctor_set(v___x_414_, 2, v___x_412_);
lean_ctor_set(v___x_414_, 3, v___x_413_);
v___x_415_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__13));
v___x_416_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__15));
v___x_417_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__17));
v___x_418_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__18));
lean_inc(v_a_406_);
v___x_419_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_419_, 0, v_a_406_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__20));
v___x_421_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__22);
v___x_422_ = lean_box(0);
lean_inc(v_currMacroScope_408_);
lean_inc(v_quotContext_407_);
v___x_423_ = l_Lean_addMacroScope(v_quotContext_407_, v___x_422_, v_currMacroScope_408_);
v___x_424_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__38));
lean_inc(v_a_406_);
v___x_425_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_425_, 0, v_a_406_);
lean_ctor_set(v___x_425_, 1, v___x_421_);
lean_ctor_set(v___x_425_, 2, v___x_423_);
lean_ctor_set(v___x_425_, 3, v___x_424_);
lean_inc(v_a_406_);
v___x_426_ = l_Lean_Syntax_node1(v_a_406_, v___x_420_, v___x_425_);
lean_inc(v_a_406_);
v___x_427_ = l_Lean_Syntax_node2(v_a_406_, v___x_417_, v___x_419_, v___x_426_);
v___x_428_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__40);
v___x_429_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__41));
lean_inc(v_currMacroScope_408_);
lean_inc(v_quotContext_407_);
v___x_430_ = l_Lean_addMacroScope(v_quotContext_407_, v___x_429_, v_currMacroScope_408_);
v___x_431_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__44));
lean_inc(v_a_406_);
v___x_432_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_432_, 0, v_a_406_);
lean_ctor_set(v___x_432_, 1, v___x_428_);
lean_ctor_set(v___x_432_, 2, v___x_430_);
lean_ctor_set(v___x_432_, 3, v___x_431_);
lean_inc(v_a_406_);
v___x_433_ = l_Lean_Syntax_node1(v_a_406_, v___x_415_, v___x_307_);
lean_inc(v_a_406_);
v___x_434_ = l_Lean_Syntax_node2(v_a_406_, v___x_409_, v___x_432_, v___x_433_);
v___x_435_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__45));
lean_inc(v_a_406_);
v___x_436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_436_, 0, v_a_406_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
lean_inc(v_a_406_);
v___x_437_ = l_Lean_Syntax_node3(v_a_406_, v___x_416_, v___x_427_, v___x_434_, v___x_436_);
lean_inc(v_a_406_);
v___x_438_ = l_Lean_Syntax_node2(v_a_406_, v___x_415_, v_snd_303_, v___x_437_);
v___x_439_ = l_Lean_Syntax_node2(v_a_406_, v___x_409_, v___x_414_, v___x_438_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_439_);
lean_ctor_set(v___x_305_, 0, v___x_308_);
v___x_441_ = v___x_305_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
v_a_286_ = v___x_441_;
goto v___jp_285_;
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v___x_308_);
lean_dec(v___x_307_);
lean_del_object(v___x_305_);
lean_dec(v_snd_303_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v_a_276_);
v_a_443_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_405_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_405_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec(v_a_294_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec_ref(v_b_277_);
lean_dec(v_a_276_);
v_a_452_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_300_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_300_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_a_294_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec_ref(v_b_277_);
lean_dec(v_a_276_);
v_a_460_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_298_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_298_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec_ref(v_b_277_);
lean_dec(v_a_276_);
v_a_468_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_293_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_293_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_add(v_a_276_, v___x_287_);
lean_dec(v_a_276_);
v_a_276_ = v___x_288_;
v_b_277_ = v_a_286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___boxed(lean_object* v_upperBound_476_, lean_object* v___x_477_, lean_object* v_xs_478_, lean_object* v_allIndVals_479_, lean_object* v_ctx_480_, lean_object* v_a_481_, lean_object* v_b_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg(v_upperBound_476_, v___x_477_, v_xs_478_, v_allIndVals_479_, v_ctx_480_, v_a_481_, v_b_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec_ref(v_ctx_480_);
lean_dec_ref(v_allIndVals_479_);
lean_dec_ref(v_xs_478_);
lean_dec(v___x_477_);
lean_dec(v_upperBound_476_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(size_t v_sz_491_, size_t v_i_492_, lean_object* v_bs_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_lt(v_i_492_, v_sz_491_);
if (v___x_494_ == 0)
{
return v_bs_493_;
}
else
{
lean_object* v_v_495_; lean_object* v___x_496_; lean_object* v_bs_x27_497_; size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v_v_495_ = lean_array_uget(v_bs_493_, v_i_492_);
v___x_496_ = lean_unsigned_to_nat(0u);
v_bs_x27_497_ = lean_array_uset(v_bs_493_, v_i_492_, v___x_496_);
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_add(v_i_492_, v___x_498_);
v___x_500_ = lean_array_uset(v_bs_x27_497_, v_i_492_, v_v_495_);
v_i_492_ = v___x_499_;
v_bs_493_ = v___x_500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1___boxed(lean_object* v_sz_502_, lean_object* v_i_503_, lean_object* v_bs_504_){
_start:
{
size_t v_sz_boxed_505_; size_t v_i_boxed_506_; lean_object* v_res_507_; 
v_sz_boxed_505_ = lean_unbox_usize(v_sz_502_);
lean_dec(v_sz_502_);
v_i_boxed_506_ = lean_unbox_usize(v_i_503_);
lean_dec(v_i_503_);
v_res_507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_boxed_505_, v_i_boxed_506_, v_bs_504_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(lean_object* v_upperBound_515_, lean_object* v_a_516_, lean_object* v_b_517_, lean_object* v___y_518_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = lean_nat_dec_lt(v_a_516_, v_upperBound_515_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_dec(v_a_516_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v_b_517_);
return v___x_521_;
}
else
{
lean_object* v_ref_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_ref_522_ = lean_ctor_get(v___y_518_, 5);
v___x_523_ = 0;
v___x_524_ = l_Lean_SourceInfo_fromRef(v_ref_522_, v___x_523_);
v___x_525_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1));
v___x_526_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2));
lean_inc(v___x_524_);
v___x_527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_524_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_Syntax_node1(v___x_524_, v___x_525_, v___x_527_);
v___x_529_ = lean_array_push(v_b_517_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_add(v_a_516_, v___x_530_);
lean_dec(v_a_516_);
v_a_516_ = v___x_531_;
v_b_517_ = v___x_529_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_533_, lean_object* v_a_534_, lean_object* v_b_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_upperBound_533_, v_a_534_, v_b_535_, v___y_536_);
lean_dec_ref(v___y_536_);
lean_dec(v_upperBound_533_);
return v_res_538_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Array_mkArray0(lean_box(0));
return v___x_546_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__8(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__7));
v___x_556_ = l_Lean_mkAtom(v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1(lean_object* v_indVal_558_, lean_object* v___x_559_, lean_object* v_alts_560_, lean_object* v_snd_561_, lean_object* v_numFields_562_, lean_object* v_allIndVals_563_, lean_object* v_ctx_564_, lean_object* v___f_565_, lean_object* v_head_566_, lean_object* v_xs_567_, lean_object* v_x_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_numParams_576_; lean_object* v_numIndices_577_; lean_object* v___x_578_; 
v_numParams_576_ = lean_ctor_get(v_indVal_558_, 1);
v_numIndices_577_ = lean_ctor_get(v_indVal_558_, 2);
lean_inc_ref(v_alts_560_);
lean_inc(v___x_559_);
v___x_578_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_numIndices_577_, v___x_559_, v_alts_560_, v___y_573_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_578_);
lean_inc(v___x_559_);
v___x_580_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_numParams_576_, v___x_559_, v_alts_560_, v___y_573_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref(v___x_580_);
v___x_582_ = l_Nat_reprFast(v_snd_561_);
v___x_583_ = lean_box(2);
v___x_584_ = l_Lean_Syntax_mkNumLit(v___x_582_, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_a_581_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
v___x_586_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg(v_numFields_562_, v_numParams_576_, v_xs_567_, v_allIndVals_563_, v_ctx_564_, v___x_559_, v___x_585_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref(v___x_586_);
lean_inc_ref(v___f_565_);
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
v___x_588_ = lean_apply_7(v___f_565_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, lean_box(0));
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref(v___x_588_);
v___x_590_ = lean_apply_7(v___f_565_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, lean_box(0));
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_632_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_632_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_632_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_632_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_fst_595_; lean_object* v_snd_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_631_; 
v_fst_595_ = lean_ctor_get(v_a_587_, 0);
v_snd_596_ = lean_ctor_get(v_a_587_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_a_587_);
if (v_isSharedCheck_631_ == 0)
{
v___x_598_ = v_a_587_;
v_isShared_599_ = v_isSharedCheck_631_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_snd_596_);
lean_inc(v_fst_595_);
lean_dec(v_a_587_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_631_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_600_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__6));
v___x_601_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__0));
lean_inc(v_a_589_);
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 2);
lean_ctor_set(v___x_598_, 1, v___x_601_);
lean_ctor_set(v___x_598_, 0, v_a_589_);
v___x_603_ = v___x_598_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_589_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_601_);
v___x_603_ = v_reuseFailAlloc_630_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; size_t v_sz_616_; size_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_604_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__2));
v___x_605_ = lean_mk_syntax_ident(v_head_566_);
lean_inc(v_a_589_);
v___x_606_ = l_Lean_Syntax_node2(v_a_589_, v___x_604_, v___x_603_, v___x_605_);
v___x_607_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__13));
v___x_608_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3);
v___x_609_ = l_Array_append___redArg(v___x_608_, v_fst_595_);
lean_dec(v_fst_595_);
lean_inc(v_a_589_);
v___x_610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_610_, 0, v_a_589_);
lean_ctor_set(v___x_610_, 1, v___x_607_);
lean_ctor_set(v___x_610_, 2, v___x_609_);
v___x_611_ = l_Lean_Syntax_node2(v_a_589_, v___x_600_, v___x_606_, v___x_610_);
v___x_612_ = lean_array_push(v_a_579_, v___x_611_);
v___x_613_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__5));
v___x_614_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__6));
lean_inc(v_a_591_);
v___x_615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_615_, 0, v_a_591_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v_sz_616_ = lean_array_size(v___x_612_);
v___x_617_ = ((size_t)0ULL);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_616_, v___x_617_, v___x_612_);
v___x_619_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__8);
v___x_620_ = l_Lean_mkSepArray(v___x_618_, v___x_619_);
lean_dec_ref(v___x_618_);
v___x_621_ = l_Array_append___redArg(v___x_608_, v___x_620_);
lean_dec_ref(v___x_620_);
lean_inc(v_a_591_);
v___x_622_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_622_, 0, v_a_591_);
lean_ctor_set(v___x_622_, 1, v___x_607_);
lean_ctor_set(v___x_622_, 2, v___x_621_);
lean_inc(v_a_591_);
v___x_623_ = l_Lean_Syntax_node1(v_a_591_, v___x_607_, v___x_622_);
v___x_624_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__9));
lean_inc(v_a_591_);
v___x_625_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_625_, 0, v_a_591_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_Syntax_node4(v_a_591_, v___x_613_, v___x_615_, v___x_623_, v___x_625_, v_snd_596_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_626_);
v___x_628_ = v___x_593_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_a_589_);
lean_dec(v_a_587_);
lean_dec(v_a_579_);
lean_dec(v_head_566_);
v_a_633_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_590_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_590_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v_a_587_);
lean_dec(v_a_579_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v_head_566_);
lean_dec_ref(v___f_565_);
v_a_641_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_588_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_588_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_a_579_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v_head_566_);
lean_dec_ref(v___f_565_);
v_a_649_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_586_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_586_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v_a_579_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v_head_566_);
lean_dec_ref(v___f_565_);
lean_dec(v_snd_561_);
lean_dec(v___x_559_);
v_a_657_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_580_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_580_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v_head_566_);
lean_dec_ref(v___f_565_);
lean_dec(v_snd_561_);
lean_dec_ref(v_alts_560_);
lean_dec(v___x_559_);
v_a_665_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_578_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_578_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_673_ = _args[0];
lean_object* v___x_674_ = _args[1];
lean_object* v_alts_675_ = _args[2];
lean_object* v_snd_676_ = _args[3];
lean_object* v_numFields_677_ = _args[4];
lean_object* v_allIndVals_678_ = _args[5];
lean_object* v_ctx_679_ = _args[6];
lean_object* v___f_680_ = _args[7];
lean_object* v_head_681_ = _args[8];
lean_object* v_xs_682_ = _args[9];
lean_object* v_x_683_ = _args[10];
lean_object* v___y_684_ = _args[11];
lean_object* v___y_685_ = _args[12];
lean_object* v___y_686_ = _args[13];
lean_object* v___y_687_ = _args[14];
lean_object* v___y_688_ = _args[15];
lean_object* v___y_689_ = _args[16];
lean_object* v___y_690_ = _args[17];
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1(v_indVal_673_, v___x_674_, v_alts_675_, v_snd_676_, v_numFields_677_, v_allIndVals_678_, v_ctx_679_, v___f_680_, v_head_681_, v_xs_682_, v_x_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec_ref(v_x_683_);
lean_dec_ref(v_xs_682_);
lean_dec_ref(v_ctx_679_);
lean_dec_ref(v_allIndVals_678_);
lean_dec(v_numFields_677_);
lean_dec_ref(v_indVal_673_);
return v_res_691_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(lean_object* v_msg_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_toApplicative_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_800_; 
v___x_707_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0);
v___x_708_ = l_ReaderT_instMonad___redArg(v___x_707_);
v_toApplicative_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v___x_708_, 1);
lean_dec(v_unused_801_);
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_800_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_toApplicative_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_800_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_toFunctor_713_; lean_object* v_toSeq_714_; lean_object* v_toSeqLeft_715_; lean_object* v_toSeqRight_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_798_; 
v_toFunctor_713_ = lean_ctor_get(v_toApplicative_709_, 0);
v_toSeq_714_ = lean_ctor_get(v_toApplicative_709_, 2);
v_toSeqLeft_715_ = lean_ctor_get(v_toApplicative_709_, 3);
v_toSeqRight_716_ = lean_ctor_get(v_toApplicative_709_, 4);
v_isSharedCheck_798_ = !lean_is_exclusive(v_toApplicative_709_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v_toApplicative_709_, 1);
lean_dec(v_unused_799_);
v___x_718_ = v_toApplicative_709_;
v_isShared_719_ = v_isSharedCheck_798_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_toSeqRight_716_);
lean_inc(v_toSeqLeft_715_);
lean_inc(v_toSeq_714_);
lean_inc(v_toFunctor_713_);
lean_dec(v_toApplicative_709_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_798_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___f_720_; lean_object* v___f_721_; lean_object* v___f_722_; lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___f_725_; lean_object* v___f_726_; lean_object* v___f_727_; lean_object* v___x_729_; 
v___f_720_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__1));
v___f_721_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_713_);
v___f_722_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_722_, 0, v_toFunctor_713_);
v___f_723_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_723_, 0, v_toFunctor_713_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___f_722_);
lean_ctor_set(v___x_724_, 1, v___f_723_);
v___f_725_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_725_, 0, v_toSeqRight_716_);
v___f_726_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_726_, 0, v_toSeqLeft_715_);
v___f_727_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_727_, 0, v_toSeq_714_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 4, v___f_725_);
lean_ctor_set(v___x_718_, 3, v___f_726_);
lean_ctor_set(v___x_718_, 2, v___f_727_);
lean_ctor_set(v___x_718_, 1, v___f_720_);
lean_ctor_set(v___x_718_, 0, v___x_724_);
v___x_729_ = v___x_718_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___f_720_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v___f_727_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v___f_726_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v___f_725_);
v___x_729_ = v_reuseFailAlloc_797_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 1, v___f_721_);
lean_ctor_set(v___x_711_, 0, v___x_729_);
v___x_731_ = v___x_711_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___f_721_);
v___x_731_ = v_reuseFailAlloc_796_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; lean_object* v_toApplicative_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_794_; 
v___x_732_ = l_ReaderT_instMonad___redArg(v___x_731_);
v_toApplicative_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v___x_732_, 1);
lean_dec(v_unused_795_);
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_794_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_toApplicative_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_794_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_toFunctor_737_; lean_object* v_toSeq_738_; lean_object* v_toSeqLeft_739_; lean_object* v_toSeqRight_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_792_; 
v_toFunctor_737_ = lean_ctor_get(v_toApplicative_733_, 0);
v_toSeq_738_ = lean_ctor_get(v_toApplicative_733_, 2);
v_toSeqLeft_739_ = lean_ctor_get(v_toApplicative_733_, 3);
v_toSeqRight_740_ = lean_ctor_get(v_toApplicative_733_, 4);
v_isSharedCheck_792_ = !lean_is_exclusive(v_toApplicative_733_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_toApplicative_733_, 1);
lean_dec(v_unused_793_);
v___x_742_ = v_toApplicative_733_;
v_isShared_743_ = v_isSharedCheck_792_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_toSeqRight_740_);
lean_inc(v_toSeqLeft_739_);
lean_inc(v_toSeq_738_);
lean_inc(v_toFunctor_737_);
lean_dec(v_toApplicative_733_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_792_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_753_; 
v___f_744_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__3));
v___f_745_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_737_);
v___f_746_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_746_, 0, v_toFunctor_737_);
v___f_747_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_747_, 0, v_toFunctor_737_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___f_746_);
lean_ctor_set(v___x_748_, 1, v___f_747_);
v___f_749_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_749_, 0, v_toSeqRight_740_);
v___f_750_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_750_, 0, v_toSeqLeft_739_);
v___f_751_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_751_, 0, v_toSeq_738_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 4, v___f_749_);
lean_ctor_set(v___x_742_, 3, v___f_750_);
lean_ctor_set(v___x_742_, 2, v___f_751_);
lean_ctor_set(v___x_742_, 1, v___f_744_);
lean_ctor_set(v___x_742_, 0, v___x_748_);
v___x_753_ = v___x_742_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___f_744_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v___f_751_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v___f_750_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v___f_749_);
v___x_753_ = v_reuseFailAlloc_791_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___f_745_);
lean_ctor_set(v___x_735_, 0, v___x_753_);
v___x_755_ = v___x_735_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___f_745_);
v___x_755_ = v_reuseFailAlloc_790_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v_toApplicative_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_788_; 
v___x_756_ = l_ReaderT_instMonad___redArg(v___x_755_);
v_toApplicative_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_756_, 1);
lean_dec(v_unused_789_);
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_788_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_toApplicative_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_788_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_toFunctor_761_; lean_object* v_toSeq_762_; lean_object* v_toSeqLeft_763_; lean_object* v_toSeqRight_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_786_; 
v_toFunctor_761_ = lean_ctor_get(v_toApplicative_757_, 0);
v_toSeq_762_ = lean_ctor_get(v_toApplicative_757_, 2);
v_toSeqLeft_763_ = lean_ctor_get(v_toApplicative_757_, 3);
v_toSeqRight_764_ = lean_ctor_get(v_toApplicative_757_, 4);
v_isSharedCheck_786_ = !lean_is_exclusive(v_toApplicative_757_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v_toApplicative_757_, 1);
lean_dec(v_unused_787_);
v___x_766_ = v_toApplicative_757_;
v_isShared_767_ = v_isSharedCheck_786_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_toSeqRight_764_);
lean_inc(v_toSeqLeft_763_);
lean_inc(v_toSeq_762_);
lean_inc(v_toFunctor_761_);
lean_dec(v_toApplicative_757_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_786_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___f_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_777_; 
v___f_768_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__5));
v___f_769_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_761_);
v___f_770_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_770_, 0, v_toFunctor_761_);
v___f_771_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_771_, 0, v_toFunctor_761_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___f_770_);
lean_ctor_set(v___x_772_, 1, v___f_771_);
v___f_773_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_773_, 0, v_toSeqRight_764_);
v___f_774_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_774_, 0, v_toSeqLeft_763_);
v___f_775_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_775_, 0, v_toSeq_762_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 4, v___f_773_);
lean_ctor_set(v___x_766_, 3, v___f_774_);
lean_ctor_set(v___x_766_, 2, v___f_775_);
lean_ctor_set(v___x_766_, 1, v___f_768_);
lean_ctor_set(v___x_766_, 0, v___x_772_);
v___x_777_ = v___x_766_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___f_768_);
lean_ctor_set(v_reuseFailAlloc_785_, 2, v___f_775_);
lean_ctor_set(v_reuseFailAlloc_785_, 3, v___f_774_);
lean_ctor_set(v_reuseFailAlloc_785_, 4, v___f_773_);
v___x_777_ = v_reuseFailAlloc_785_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_779_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v___f_769_);
lean_ctor_set(v___x_759_, 0, v___x_777_);
v___x_779_ = v___x_759_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v___f_769_);
v___x_779_ = v_reuseFailAlloc_784_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_30649__overap_782_; lean_object* v___x_783_; 
v___x_780_ = lean_box(0);
v___x_781_ = l_instInhabitedOfMonad___redArg(v___x_779_, v___x_780_);
v___x_30649__overap_782_ = lean_panic_fn(v___x_781_, v_msg_699_);
v___x_783_ = lean_apply_7(v___x_30649__overap_782_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, lean_box(0));
return v___x_783_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(v_msg_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; lean_object* v_env_818_; lean_object* v___x_819_; lean_object* v_mctx_820_; lean_object* v_lctx_821_; lean_object* v_options_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_817_ = lean_st_ref_get(v___y_815_);
v_env_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc_ref(v_env_818_);
lean_dec(v___x_817_);
v___x_819_ = lean_st_ref_get(v___y_813_);
v_mctx_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc_ref(v_mctx_820_);
lean_dec(v___x_819_);
v_lctx_821_ = lean_ctor_get(v___y_812_, 2);
v_options_822_ = lean_ctor_get(v___y_814_, 2);
lean_inc_ref(v_options_822_);
lean_inc_ref(v_lctx_821_);
v___x_823_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_823_, 0, v_env_818_);
lean_ctor_set(v___x_823_, 1, v_mctx_820_);
lean_ctor_set(v___x_823_, 2, v_lctx_821_);
lean_ctor_set(v___x_823_, 3, v_options_822_);
v___x_824_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v_msgData_811_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msgData_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_832_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_box(1);
v___x_834_ = l_Lean_MessageData_ofFormat(v___x_833_);
return v___x_834_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2));
v___x_839_ = l_Lean_MessageData_ofFormat(v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
if (lean_obj_tag(v_x_841_) == 0)
{
return v_x_840_;
}
else
{
lean_object* v_head_842_; lean_object* v_tail_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_865_; 
v_head_842_ = lean_ctor_get(v_x_841_, 0);
v_tail_843_ = lean_ctor_get(v_x_841_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_x_841_);
if (v_isSharedCheck_865_ == 0)
{
v___x_845_ = v_x_841_;
v_isShared_846_ = v_isSharedCheck_865_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_tail_843_);
lean_inc(v_head_842_);
lean_dec(v_x_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_865_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_before_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_863_; 
v_before_847_ = lean_ctor_get(v_head_842_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_head_842_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v_head_842_, 1);
lean_dec(v_unused_864_);
v___x_849_ = v_head_842_;
v_isShared_850_ = v_isSharedCheck_863_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_before_847_);
lean_dec(v_head_842_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_863_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_850_ == 0)
{
lean_ctor_set_tag(v___x_849_, 7);
lean_ctor_set(v___x_849_, 1, v___x_851_);
lean_ctor_set(v___x_849_, 0, v_x_840_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_x_840_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_851_);
v___x_853_ = v_reuseFailAlloc_862_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_854_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 7);
lean_ctor_set(v___x_845_, 1, v___x_854_);
lean_ctor_set(v___x_845_, 0, v___x_853_);
v___x_856_ = v___x_845_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_861_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = l_Lean_MessageData_ofSyntax(v_before_847_);
v___x_858_ = l_Lean_indentD(v___x_857_);
v___x_859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_856_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v_x_840_ = v___x_859_;
v_x_841_ = v_tail_843_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__10(lean_object* v_opts_866_, lean_object* v_opt_867_){
_start:
{
lean_object* v_name_868_; lean_object* v_defValue_869_; lean_object* v_map_870_; lean_object* v___x_871_; 
v_name_868_ = lean_ctor_get(v_opt_867_, 0);
v_defValue_869_ = lean_ctor_get(v_opt_867_, 1);
v_map_870_ = lean_ctor_get(v_opts_866_, 0);
v___x_871_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_870_, v_name_868_);
if (lean_obj_tag(v___x_871_) == 0)
{
uint8_t v___x_872_; 
v___x_872_ = lean_unbox(v_defValue_869_);
return v___x_872_;
}
else
{
lean_object* v_val_873_; 
v_val_873_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_val_873_);
lean_dec_ref(v___x_871_);
if (lean_obj_tag(v_val_873_) == 1)
{
uint8_t v_v_874_; 
v_v_874_ = lean_ctor_get_uint8(v_val_873_, 0);
lean_dec_ref(v_val_873_);
return v_v_874_;
}
else
{
uint8_t v___x_875_; 
lean_dec(v_val_873_);
v___x_875_ = lean_unbox(v_defValue_869_);
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_opts_876_, lean_object* v_opt_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__10(v_opts_876_, v_opt_877_);
lean_dec_ref(v_opt_877_);
lean_dec_ref(v_opts_876_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_884_ = l_Lean_MessageData_ofFormat(v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_885_, lean_object* v_macroStack_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_options_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v_options_889_ = lean_ctor_get(v___y_887_, 2);
v___x_890_ = l_Lean_Elab_pp_macroStack;
v___x_891_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__10(v_options_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_dec(v_macroStack_886_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v_msgData_885_);
return v___x_892_;
}
else
{
if (lean_obj_tag(v_macroStack_886_) == 0)
{
lean_object* v___x_893_; 
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v_msgData_885_);
return v___x_893_;
}
else
{
lean_object* v_head_894_; lean_object* v_after_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_910_; 
v_head_894_ = lean_ctor_get(v_macroStack_886_, 0);
lean_inc(v_head_894_);
v_after_895_ = lean_ctor_get(v_head_894_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_head_894_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v_head_894_, 0);
lean_dec(v_unused_911_);
v___x_897_ = v_head_894_;
v_isShared_898_ = v_isSharedCheck_910_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_after_895_);
lean_dec(v_head_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_910_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 7);
lean_ctor_set(v___x_897_, 1, v___x_899_);
lean_ctor_set(v___x_897_, 0, v_msgData_885_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_msgData_885_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v___x_899_);
v___x_901_ = v_reuseFailAlloc_909_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_msgData_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_902_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_MessageData_ofSyntax(v_after_895_);
v___x_905_ = l_Lean_indentD(v___x_904_);
v_msgData_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_906_, 0, v___x_903_);
lean_ctor_set(v_msgData_906_, 1, v___x_905_);
v___x_907_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(v_msgData_906_, v_macroStack_886_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_912_, lean_object* v_macroStack_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_912_, v_macroStack_913_, v___y_914_);
lean_dec_ref(v___y_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_ref_925_; lean_object* v___x_926_; lean_object* v_a_927_; lean_object* v_macroStack_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
v_ref_925_ = lean_ctor_get(v___y_922_, 5);
v___x_926_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msg_917_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v_macroStack_928_ = lean_ctor_get(v___y_918_, 1);
lean_inc(v_macroStack_928_);
lean_dec_ref(v___y_918_);
lean_inc(v_macroStack_928_);
v___x_929_ = l_Lean_Elab_getBetterRef(v_ref_925_, v_macroStack_928_);
v___x_930_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_927_, v_macroStack_928_, v___y_922_);
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_939_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_929_);
lean_ctor_set(v___x_935_, 1, v_a_931_);
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 1);
lean_ctor_set(v___x_933_, 0, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v_msg_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
return v_res_948_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__0));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__2));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_958_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__6));
v___x_959_ = lean_unsigned_to_nat(11u);
v___x_960_ = lean_unsigned_to_nat(122u);
v___x_961_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__5));
v___x_962_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__4));
v___x_963_ = l_mkPanicMessageWithDecl(v___x_962_, v___x_961_, v___x_960_, v___x_959_, v___x_958_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(lean_object* v_constName_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_980_; lean_object* v_env_981_; uint8_t v___x_982_; lean_object* v___x_983_; 
v___x_980_ = lean_st_ref_get(v___y_970_);
v_env_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc_ref(v_env_981_);
lean_dec(v___x_980_);
v___x_982_ = 0;
lean_inc(v_constName_964_);
v___x_983_ = l_Lean_Environment_findAsync_x3f(v_env_981_, v_constName_964_, v___x_982_);
if (lean_obj_tag(v___x_983_) == 1)
{
lean_object* v_val_984_; uint8_t v_kind_985_; 
v_val_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_val_984_);
lean_dec_ref(v___x_983_);
v_kind_985_ = lean_ctor_get_uint8(v_val_984_, sizeof(void*)*3);
if (v_kind_985_ == 6)
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_984_);
if (lean_obj_tag(v___x_986_) == 6)
{
lean_object* v_val_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v_constName_964_);
v_val_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_val_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 0);
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_val_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec_ref(v___x_986_);
v___x_995_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
lean_inc(v___y_966_);
lean_inc_ref(v___y_965_);
v___x_996_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(v___x_995_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1005_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
if (lean_obj_tag(v_a_997_) == 0)
{
lean_del_object(v___x_999_);
goto v___jp_972_;
}
else
{
lean_object* v_val_1001_; lean_object* v___x_1003_; 
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v_constName_964_);
v_val_1001_ = lean_ctor_get(v_a_997_, 0);
lean_inc(v_val_1001_);
lean_dec_ref(v_a_997_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_val_1001_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_val_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v_constName_964_);
v_a_1006_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_996_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_996_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
else
{
lean_dec(v_val_984_);
goto v___jp_972_;
}
}
else
{
lean_dec(v___x_983_);
goto v___jp_972_;
}
v___jp_972_:
{
lean_object* v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_973_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1);
v___x_974_ = 0;
v___x_975_ = l_Lean_MessageData_ofConstName(v_constName_964_, v___x_974_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_973_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v___x_978_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___boxed(lean_object* v_constName_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(v_constName_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(lean_object* v_indVal_1026_, lean_object* v_allIndVals_1027_, lean_object* v_ctx_1028_, lean_object* v_as_x27_1029_, lean_object* v_b_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
if (lean_obj_tag(v_as_x27_1029_) == 0)
{
lean_object* v___x_1038_; 
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec_ref(v_ctx_1028_);
lean_dec_ref(v_allIndVals_1027_);
lean_dec_ref(v_indVal_1026_);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_b_1030_);
return v___x_1038_;
}
else
{
lean_object* v_head_1039_; lean_object* v_tail_1040_; lean_object* v___x_1041_; 
v_head_1039_ = lean_ctor_get(v_as_x27_1029_, 0);
lean_inc(v_head_1039_);
v_tail_1040_ = lean_ctor_get(v_as_x27_1029_, 1);
lean_inc(v_tail_1040_);
lean_dec_ref(v_as_x27_1029_);
lean_inc(v___y_1036_);
lean_inc_ref(v___y_1035_);
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
lean_inc(v_head_1039_);
v___x_1041_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(v_head_1039_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v_toConstantVal_1043_; lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1073_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref(v___x_1041_);
v_toConstantVal_1043_ = lean_ctor_get(v_a_1042_, 0);
lean_inc_ref(v_toConstantVal_1043_);
v_fst_1044_ = lean_ctor_get(v_b_1030_, 0);
v_snd_1045_ = lean_ctor_get(v_b_1030_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_b_1030_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1047_ = v_b_1030_;
v_isShared_1048_ = v_isSharedCheck_1073_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_snd_1045_);
lean_inc(v_fst_1044_);
lean_dec(v_b_1030_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1073_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_numFields_1049_; lean_object* v_type_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v_alts_1053_; lean_object* v___f_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; 
v_numFields_1049_ = lean_ctor_get(v_a_1042_, 4);
lean_inc(v_numFields_1049_);
lean_dec(v_a_1042_);
v_type_1050_ = lean_ctor_get(v_toConstantVal_1043_, 2);
lean_inc_ref(v_type_1050_);
lean_dec_ref(v_toConstantVal_1043_);
v___f_1051_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___closed__0));
v___x_1052_ = lean_unsigned_to_nat(0u);
v_alts_1053_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___closed__1));
lean_inc_ref(v_ctx_1028_);
lean_inc_ref(v_allIndVals_1027_);
lean_inc(v_snd_1045_);
lean_inc_ref(v_indVal_1026_);
v___f_1054_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___boxed), 18, 9);
lean_closure_set(v___f_1054_, 0, v_indVal_1026_);
lean_closure_set(v___f_1054_, 1, v___x_1052_);
lean_closure_set(v___f_1054_, 2, v_alts_1053_);
lean_closure_set(v___f_1054_, 3, v_snd_1045_);
lean_closure_set(v___f_1054_, 4, v_numFields_1049_);
lean_closure_set(v___f_1054_, 5, v_allIndVals_1027_);
lean_closure_set(v___f_1054_, 6, v_ctx_1028_);
lean_closure_set(v___f_1054_, 7, v___f_1051_);
lean_closure_set(v___f_1054_, 8, v_head_1039_);
v___x_1055_ = 0;
lean_inc(v___y_1036_);
lean_inc_ref(v___y_1035_);
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
v___x_1056_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_type_1050_, v___f_1054_, v___x_1055_, v___x_1055_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = lean_array_push(v_fst_1044_, v_a_1057_);
v___x_1059_ = lean_unsigned_to_nat(1u);
v___x_1060_ = lean_nat_add(v_snd_1045_, v___x_1059_);
lean_dec(v_snd_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___x_1060_);
lean_ctor_set(v___x_1047_, 0, v___x_1058_);
v___x_1062_ = v___x_1047_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
v_as_x27_1029_ = v_tail_1040_;
v_b_1030_ = v___x_1062_;
goto _start;
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_del_object(v___x_1047_);
lean_dec(v_snd_1045_);
lean_dec(v_fst_1044_);
lean_dec(v_tail_1040_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec_ref(v_ctx_1028_);
lean_dec_ref(v_allIndVals_1027_);
lean_dec_ref(v_indVal_1026_);
v_a_1065_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1056_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1056_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec(v_tail_1040_);
lean_dec(v_head_1039_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec_ref(v_b_1030_);
lean_dec_ref(v_ctx_1028_);
lean_dec_ref(v_allIndVals_1027_);
lean_dec_ref(v_indVal_1026_);
v_a_1074_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1041_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1041_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___boxed(lean_object* v_indVal_1082_, lean_object* v_allIndVals_1083_, lean_object* v_ctx_1084_, lean_object* v_as_x27_1085_, lean_object* v_b_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_indVal_1082_, v_allIndVals_1083_, v_ctx_1084_, v_as_x27_1085_, v_b_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(lean_object* v_ctx_1098_, lean_object* v_indVal_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_all_1107_; lean_object* v_ctors_1108_; lean_object* v_allIndVals_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_all_1107_ = lean_ctor_get(v_indVal_1099_, 3);
v_ctors_1108_ = lean_ctor_get(v_indVal_1099_, 4);
lean_inc(v_ctors_1108_);
lean_inc(v_all_1107_);
v_allIndVals_1109_ = lean_array_mk(v_all_1107_);
v___x_1110_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0));
v___x_1111_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_indVal_1099_, v_allIndVals_1109_, v_ctx_1098_, v_ctors_1108_, v___x_1110_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1123_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_fst_1116_; size_t v_sz_1117_; size_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v_fst_1116_ = lean_ctor_get(v_a_1112_, 0);
lean_inc(v_fst_1116_);
lean_dec(v_a_1112_);
v_sz_1117_ = lean_array_size(v_fst_1116_);
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(v_sz_1117_, v___x_1118_, v_fst_1116_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1119_);
v___x_1121_ = v___x_1114_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
v_a_1124_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1111_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1111_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___boxed(lean_object* v_ctx_1132_, lean_object* v_indVal_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(v_ctx_1132_, v_indVal_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(lean_object* v_upperBound_1142_, lean_object* v___x_1143_, lean_object* v_xs_1144_, lean_object* v_allIndVals_1145_, lean_object* v_ctx_1146_, lean_object* v_inst_1147_, lean_object* v_R_1148_, lean_object* v_a_1149_, lean_object* v_b_1150_, lean_object* v_c_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg(v_upperBound_1142_, v___x_1143_, v_xs_1144_, v_allIndVals_1145_, v_ctx_1146_, v_a_1149_, v_b_1150_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_1160_ = _args[0];
lean_object* v___x_1161_ = _args[1];
lean_object* v_xs_1162_ = _args[2];
lean_object* v_allIndVals_1163_ = _args[3];
lean_object* v_ctx_1164_ = _args[4];
lean_object* v_inst_1165_ = _args[5];
lean_object* v_R_1166_ = _args[6];
lean_object* v_a_1167_ = _args[7];
lean_object* v_b_1168_ = _args[8];
lean_object* v_c_1169_ = _args[9];
lean_object* v___y_1170_ = _args[10];
lean_object* v___y_1171_ = _args[11];
lean_object* v___y_1172_ = _args[12];
lean_object* v___y_1173_ = _args[13];
lean_object* v___y_1174_ = _args[14];
lean_object* v___y_1175_ = _args[15];
lean_object* v___y_1176_ = _args[16];
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(v_upperBound_1160_, v___x_1161_, v_xs_1162_, v_allIndVals_1163_, v_ctx_1164_, v_inst_1165_, v_R_1166_, v_a_1167_, v_b_1168_, v_c_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec_ref(v_ctx_1164_);
lean_dec_ref(v_allIndVals_1163_);
lean_dec_ref(v_xs_1162_);
lean_dec(v___x_1161_);
lean_dec(v_upperBound_1160_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3(lean_object* v_upperBound_1178_, lean_object* v_inst_1179_, lean_object* v_R_1180_, lean_object* v_a_1181_, lean_object* v_b_1182_, lean_object* v_c_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_upperBound_1178_, v_a_1181_, v_b_1182_, v___y_1188_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___boxed(lean_object* v_upperBound_1192_, lean_object* v_inst_1193_, lean_object* v_R_1194_, lean_object* v_a_1195_, lean_object* v_b_1196_, lean_object* v_c_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3(v_upperBound_1192_, v_inst_1193_, v_R_1194_, v_a_1195_, v_b_1196_, v_c_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v_upperBound_1192_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5(lean_object* v_indVal_1206_, lean_object* v_allIndVals_1207_, lean_object* v_ctx_1208_, lean_object* v_as_1209_, lean_object* v_as_x27_1210_, lean_object* v_b_1211_, lean_object* v_a_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_indVal_1206_, v_allIndVals_1207_, v_ctx_1208_, v_as_x27_1210_, v_b_1211_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___boxed(lean_object* v_indVal_1221_, lean_object* v_allIndVals_1222_, lean_object* v_ctx_1223_, lean_object* v_as_1224_, lean_object* v_as_x27_1225_, lean_object* v_b_1226_, lean_object* v_a_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5(v_indVal_1221_, v_allIndVals_1222_, v_ctx_1223_, v_as_1224_, v_as_x27_1225_, v_b_1226_, v_a_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v_as_1224_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1236_, lean_object* v_msg_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v_msg_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_msg_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0(v_00_u03b1_1246_, v_msg_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1256_, lean_object* v_macroStack_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1256_, v_macroStack_1257_, v___y_1262_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1266_, lean_object* v_macroStack_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3(v_msgData_1266_, v_macroStack_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch(lean_object* v_ctx_1289_, lean_object* v_header_1290_, lean_object* v_indVal_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v___x_1299_; 
lean_inc_ref(v_indVal_1291_);
v___x_1299_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_1290_, v_indVal_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1301_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref(v___x_1299_);
lean_inc_ref(v_a_1296_);
v___x_1301_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(v_ctx_1289_, v_indVal_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1332_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1332_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1332_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v_ref_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; size_t v_sz_1315_; size_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v_ref_1306_ = lean_ctor_get(v_a_1296_, 5);
lean_inc(v_ref_1306_);
lean_dec_ref(v_a_1296_);
v___x_1307_ = 0;
v___x_1308_ = l_Lean_SourceInfo_fromRef(v_ref_1306_, v___x_1307_);
lean_dec(v_ref_1306_);
v___x_1309_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0));
v___x_1310_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1));
lean_inc(v___x_1308_);
v___x_1311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1308_);
lean_ctor_set(v___x_1311_, 1, v___x_1309_);
v___x_1312_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__13));
v___x_1313_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3);
lean_inc(v___x_1308_);
v___x_1314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1308_);
lean_ctor_set(v___x_1314_, 1, v___x_1312_);
lean_ctor_set(v___x_1314_, 2, v___x_1313_);
v_sz_1315_ = lean_array_size(v_a_1300_);
v___x_1316_ = ((size_t)0ULL);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_1315_, v___x_1316_, v_a_1300_);
v___x_1318_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__8);
v___x_1319_ = l_Lean_mkSepArray(v___x_1317_, v___x_1318_);
lean_dec_ref(v___x_1317_);
v___x_1320_ = l_Array_append___redArg(v___x_1313_, v___x_1319_);
lean_dec_ref(v___x_1319_);
lean_inc(v___x_1308_);
v___x_1321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1308_);
lean_ctor_set(v___x_1321_, 1, v___x_1312_);
lean_ctor_set(v___x_1321_, 2, v___x_1320_);
v___x_1322_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2));
lean_inc(v___x_1308_);
v___x_1323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1308_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4));
v___x_1325_ = l_Array_append___redArg(v___x_1313_, v_a_1302_);
lean_dec(v_a_1302_);
lean_inc(v___x_1308_);
v___x_1326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1308_);
lean_ctor_set(v___x_1326_, 1, v___x_1312_);
lean_ctor_set(v___x_1326_, 2, v___x_1325_);
lean_inc(v___x_1308_);
v___x_1327_ = l_Lean_Syntax_node1(v___x_1308_, v___x_1324_, v___x_1326_);
lean_inc_ref(v___x_1314_);
v___x_1328_ = l_Lean_Syntax_node6(v___x_1308_, v___x_1310_, v___x_1311_, v___x_1314_, v___x_1314_, v___x_1321_, v___x_1323_, v___x_1327_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1328_);
v___x_1330_ = v___x_1304_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1296_);
v_a_1333_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1301_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1301_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec_ref(v_indVal_1291_);
lean_dec_ref(v_ctx_1289_);
v_a_1341_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1299_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1299_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkMatch___boxed(lean_object* v_ctx_1349_, lean_object* v_header_1350_, lean_object* v_indVal_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_Elab_Deriving_Hashable_mkMatch(v_ctx_1349_, v_header_1350_, v_indVal_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
return v_res_1359_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14));
v___x_1400_ = l_String_toRawSubstring_x27(v___x_1399_);
return v___x_1400_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28));
v___x_1432_ = l_String_toRawSubstring_x27(v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction(lean_object* v_ctx_1475_, lean_object* v_i_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_typeInfos_1484_; lean_object* v_auxFunNames_1485_; uint8_t v_usePartial_1486_; lean_object* v___x_1487_; lean_object* v_indVal_1488_; lean_object* v___x_1489_; 
v_typeInfos_1484_ = lean_ctor_get(v_ctx_1475_, 1);
v_auxFunNames_1485_ = lean_ctor_get(v_ctx_1475_, 2);
v_usePartial_1486_ = lean_ctor_get_uint8(v_ctx_1475_, sizeof(void*)*3);
v___x_1487_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_1488_ = lean_array_get_borrowed(v___x_1487_, v_typeInfos_1484_, v_i_1476_);
lean_inc(v_a_1482_);
lean_inc_ref(v_a_1481_);
lean_inc(v_a_1480_);
lean_inc_ref(v_a_1479_);
lean_inc(v_a_1478_);
lean_inc_ref(v_a_1477_);
lean_inc(v_indVal_1488_);
v___x_1489_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader(v_indVal_1488_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1491_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref(v___x_1489_);
lean_inc(v_a_1482_);
lean_inc_ref(v_a_1481_);
lean_inc(v_a_1480_);
lean_inc_ref(v_a_1479_);
lean_inc(v_a_1478_);
lean_inc_ref(v_a_1477_);
lean_inc(v_indVal_1488_);
lean_inc(v_a_1490_);
lean_inc_ref(v_ctx_1475_);
v___x_1491_ = l_Lean_Elab_Deriving_Hashable_mkMatch(v_ctx_1475_, v_a_1490_, v_indVal_1488_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1642_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1642_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1642_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v_auxFunName_1497_; lean_object* v_body_1499_; lean_object* v___y_1500_; 
v___x_1496_ = lean_box(0);
v_auxFunName_1497_ = lean_array_get(v___x_1496_, v_auxFunNames_1485_, v_i_1476_);
if (v_usePartial_1486_ == 0)
{
lean_dec(v_a_1482_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec_ref(v_ctx_1475_);
v_body_1499_ = v_a_1492_;
v___y_1500_ = v_a_1481_;
goto v___jp_1498_;
}
else
{
lean_object* v_argNames_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_argNames_1628_ = lean_ctor_get(v_a_1490_, 1);
v___x_1629_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1));
lean_inc(v_a_1482_);
lean_inc_ref(v_a_1481_);
lean_inc(v_a_1480_);
lean_inc_ref(v_a_1479_);
lean_inc(v_a_1478_);
lean_inc_ref(v_a_1477_);
lean_inc_ref(v_argNames_1628_);
v___x_1630_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_1475_, v___x_1629_, v_argNames_1628_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
lean_dec_ref(v_ctx_1475_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref(v___x_1630_);
v___x_1632_ = l_Lean_Elab_Deriving_mkLet(v_a_1631_, v_a_1492_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
lean_dec(v_a_1482_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1631_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref(v___x_1632_);
v_body_1499_ = v_a_1633_;
v___y_1500_ = v_a_1481_;
goto v___jp_1498_;
}
else
{
lean_dec(v_auxFunName_1497_);
lean_del_object(v___x_1494_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1481_);
return v___x_1632_;
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec(v_auxFunName_1497_);
lean_del_object(v___x_1494_);
lean_dec(v_a_1492_);
lean_dec(v_a_1490_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
v_a_1634_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1630_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1630_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
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
v___jp_1498_:
{
if (v_usePartial_1486_ == 0)
{
lean_object* v_binders_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1567_; 
v_binders_1501_ = lean_ctor_get(v_a_1490_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_a_1490_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; lean_object* v_unused_1569_; lean_object* v_unused_1570_; 
v_unused_1568_ = lean_ctor_get(v_a_1490_, 3);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_a_1490_, 2);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_a_1490_, 1);
lean_dec(v_unused_1570_);
v___x_1503_ = v_a_1490_;
v_isShared_1504_ = v_isSharedCheck_1567_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_binders_1501_);
lean_dec(v_a_1490_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1567_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v_ref_1505_; lean_object* v_quotContext_1506_; lean_object* v_currMacroScope_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v_ref_1505_ = lean_ctor_get(v___y_1500_, 5);
lean_inc(v_ref_1505_);
v_quotContext_1506_ = lean_ctor_get(v___y_1500_, 10);
lean_inc(v_quotContext_1506_);
v_currMacroScope_1507_ = lean_ctor_get(v___y_1500_, 11);
lean_inc(v_currMacroScope_1507_);
lean_dec_ref(v___y_1500_);
v___x_1508_ = l_Lean_SourceInfo_fromRef(v_ref_1505_, v_usePartial_1486_);
lean_dec(v_ref_1505_);
v___x_1509_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1));
v___x_1510_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3));
v___x_1511_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__13));
v___x_1512_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3);
lean_inc(v___x_1508_);
v___x_1513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1508_);
lean_ctor_set(v___x_1513_, 1, v___x_1511_);
lean_ctor_set(v___x_1513_, 2, v___x_1512_);
v___x_1514_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5));
v___x_1515_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6));
lean_inc(v___x_1508_);
v___x_1516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1508_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8));
v___x_1518_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10));
lean_inc_ref(v___x_1513_);
lean_inc(v___x_1508_);
v___x_1519_ = l_Lean_Syntax_node1(v___x_1508_, v___x_1518_, v___x_1513_);
v___x_1520_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13));
v___x_1521_ = lean_obj_once(&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15, &l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15_once, _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15);
v___x_1522_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__16));
lean_inc(v_currMacroScope_1507_);
lean_inc(v_quotContext_1506_);
v___x_1523_ = l_Lean_addMacroScope(v_quotContext_1506_, v___x_1522_, v_currMacroScope_1507_);
v___x_1524_ = lean_box(0);
lean_inc(v___x_1508_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set_tag(v___x_1503_, 3);
lean_ctor_set(v___x_1503_, 3, v___x_1524_);
lean_ctor_set(v___x_1503_, 2, v___x_1523_);
lean_ctor_set(v___x_1503_, 1, v___x_1521_);
lean_ctor_set(v___x_1503_, 0, v___x_1508_);
v___x_1526_ = v___x_1503_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1564_; 
lean_inc_ref(v___x_1513_);
lean_inc(v___x_1508_);
v___x_1527_ = l_Lean_Syntax_node2(v___x_1508_, v___x_1520_, v___x_1526_, v___x_1513_);
lean_inc(v___x_1508_);
v___x_1528_ = l_Lean_Syntax_node2(v___x_1508_, v___x_1517_, v___x_1519_, v___x_1527_);
lean_inc(v___x_1508_);
v___x_1529_ = l_Lean_Syntax_node1(v___x_1508_, v___x_1511_, v___x_1528_);
v___x_1530_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__17));
lean_inc(v___x_1508_);
v___x_1531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1508_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
lean_inc(v___x_1508_);
v___x_1532_ = l_Lean_Syntax_node3(v___x_1508_, v___x_1514_, v___x_1516_, v___x_1529_, v___x_1531_);
lean_inc(v___x_1508_);
v___x_1533_ = l_Lean_Syntax_node1(v___x_1508_, v___x_1511_, v___x_1532_);
lean_inc_ref_n(v___x_1513_, 6);
lean_inc(v___x_1508_);
v___x_1534_ = l_Lean_Syntax_node7(v___x_1508_, v___x_1510_, v___x_1513_, v___x_1533_, v___x_1513_, v___x_1513_, v___x_1513_, v___x_1513_, v___x_1513_);
v___x_1535_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19));
v___x_1536_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20));
lean_inc(v___x_1508_);
v___x_1537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1508_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22));
v___x_1539_ = lean_mk_syntax_ident(v_auxFunName_1497_);
lean_inc_ref(v___x_1513_);
lean_inc(v___x_1508_);
v___x_1540_ = l_Lean_Syntax_node2(v___x_1508_, v___x_1538_, v___x_1539_, v___x_1513_);
v___x_1541_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24));
v___x_1542_ = l_Array_append___redArg(v___x_1512_, v_binders_1501_);
lean_dec_ref(v_binders_1501_);
lean_inc(v___x_1508_);
v___x_1543_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1508_);
lean_ctor_set(v___x_1543_, 1, v___x_1511_);
lean_ctor_set(v___x_1543_, 2, v___x_1542_);
v___x_1544_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26));
v___x_1545_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27));
lean_inc(v___x_1508_);
v___x_1546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1508_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_obj_once(&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29, &l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29_once, _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29);
v___x_1548_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30));
v___x_1549_ = l_Lean_addMacroScope(v_quotContext_1506_, v___x_1548_, v_currMacroScope_1507_);
v___x_1550_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34));
lean_inc(v___x_1508_);
v___x_1551_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1508_);
lean_ctor_set(v___x_1551_, 1, v___x_1547_);
lean_ctor_set(v___x_1551_, 2, v___x_1549_);
lean_ctor_set(v___x_1551_, 3, v___x_1550_);
lean_inc(v___x_1508_);
v___x_1552_ = l_Lean_Syntax_node2(v___x_1508_, v___x_1544_, v___x_1546_, v___x_1551_);
lean_inc(v___x_1508_);
v___x_1553_ = l_Lean_Syntax_node1(v___x_1508_, v___x_1511_, v___x_1552_);
lean_inc(v___x_1508_);
v___x_1554_ = l_Lean_Syntax_node2(v___x_1508_, v___x_1541_, v___x_1543_, v___x_1553_);
v___x_1555_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36));
v___x_1556_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37));
lean_inc(v___x_1508_);
v___x_1557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1508_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40));
lean_inc_ref_n(v___x_1513_, 2);
lean_inc(v___x_1508_);
v___x_1559_ = l_Lean_Syntax_node2(v___x_1508_, v___x_1558_, v___x_1513_, v___x_1513_);
lean_inc_ref(v___x_1513_);
lean_inc(v___x_1508_);
v___x_1560_ = l_Lean_Syntax_node4(v___x_1508_, v___x_1555_, v___x_1557_, v_body_1499_, v___x_1559_, v___x_1513_);
lean_inc(v___x_1508_);
v___x_1561_ = l_Lean_Syntax_node5(v___x_1508_, v___x_1535_, v___x_1537_, v___x_1540_, v___x_1554_, v___x_1560_, v___x_1513_);
v___x_1562_ = l_Lean_Syntax_node2(v___x_1508_, v___x_1509_, v___x_1534_, v___x_1561_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1562_);
v___x_1564_ = v___x_1494_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_object* v_binders_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1624_; 
v_binders_1571_ = lean_ctor_get(v_a_1490_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_a_1490_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; lean_object* v_unused_1626_; lean_object* v_unused_1627_; 
v_unused_1625_ = lean_ctor_get(v_a_1490_, 3);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_a_1490_, 2);
lean_dec(v_unused_1626_);
v_unused_1627_ = lean_ctor_get(v_a_1490_, 1);
lean_dec(v_unused_1627_);
v___x_1573_ = v_a_1490_;
v_isShared_1574_ = v_isSharedCheck_1624_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_binders_1571_);
lean_dec(v_a_1490_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1624_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_ref_1575_; lean_object* v_quotContext_1576_; lean_object* v_currMacroScope_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
v_ref_1575_ = lean_ctor_get(v___y_1500_, 5);
lean_inc(v_ref_1575_);
v_quotContext_1576_ = lean_ctor_get(v___y_1500_, 10);
lean_inc(v_quotContext_1576_);
v_currMacroScope_1577_ = lean_ctor_get(v___y_1500_, 11);
lean_inc(v_currMacroScope_1577_);
lean_dec_ref(v___y_1500_);
v___x_1578_ = 0;
v___x_1579_ = l_Lean_SourceInfo_fromRef(v_ref_1575_, v___x_1578_);
lean_dec(v_ref_1575_);
v___x_1580_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1));
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3));
v___x_1582_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__13));
v___x_1583_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3);
lean_inc(v___x_1579_);
v___x_1584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1579_);
lean_ctor_set(v___x_1584_, 1, v___x_1582_);
lean_ctor_set(v___x_1584_, 2, v___x_1583_);
v___x_1585_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41));
v___x_1586_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42));
lean_inc(v___x_1579_);
v___x_1587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1579_);
lean_ctor_set(v___x_1587_, 1, v___x_1585_);
lean_inc(v___x_1579_);
v___x_1588_ = l_Lean_Syntax_node1(v___x_1579_, v___x_1586_, v___x_1587_);
lean_inc(v___x_1579_);
v___x_1589_ = l_Lean_Syntax_node1(v___x_1579_, v___x_1582_, v___x_1588_);
lean_inc_ref_n(v___x_1584_, 6);
lean_inc(v___x_1579_);
v___x_1590_ = l_Lean_Syntax_node7(v___x_1579_, v___x_1581_, v___x_1584_, v___x_1584_, v___x_1584_, v___x_1584_, v___x_1584_, v___x_1584_, v___x_1589_);
v___x_1591_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19));
v___x_1592_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20));
lean_inc(v___x_1579_);
v___x_1593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1579_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22));
v___x_1595_ = lean_mk_syntax_ident(v_auxFunName_1497_);
lean_inc_ref(v___x_1584_);
lean_inc(v___x_1579_);
v___x_1596_ = l_Lean_Syntax_node2(v___x_1579_, v___x_1594_, v___x_1595_, v___x_1584_);
v___x_1597_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24));
v___x_1598_ = l_Array_append___redArg(v___x_1583_, v_binders_1571_);
lean_dec_ref(v_binders_1571_);
lean_inc(v___x_1579_);
v___x_1599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1579_);
lean_ctor_set(v___x_1599_, 1, v___x_1582_);
lean_ctor_set(v___x_1599_, 2, v___x_1598_);
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26));
v___x_1601_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27));
lean_inc(v___x_1579_);
v___x_1602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1579_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v___x_1603_ = lean_obj_once(&l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29, &l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29_once, _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29);
v___x_1604_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30));
v___x_1605_ = l_Lean_addMacroScope(v_quotContext_1576_, v___x_1604_, v_currMacroScope_1577_);
v___x_1606_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45));
lean_inc(v___x_1579_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 3);
lean_ctor_set(v___x_1573_, 3, v___x_1606_);
lean_ctor_set(v___x_1573_, 2, v___x_1605_);
lean_ctor_set(v___x_1573_, 1, v___x_1603_);
lean_ctor_set(v___x_1573_, 0, v___x_1579_);
v___x_1608_ = v___x_1573_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_inc(v___x_1579_);
v___x_1609_ = l_Lean_Syntax_node2(v___x_1579_, v___x_1600_, v___x_1602_, v___x_1608_);
lean_inc(v___x_1579_);
v___x_1610_ = l_Lean_Syntax_node1(v___x_1579_, v___x_1582_, v___x_1609_);
lean_inc(v___x_1579_);
v___x_1611_ = l_Lean_Syntax_node2(v___x_1579_, v___x_1597_, v___x_1599_, v___x_1610_);
v___x_1612_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36));
v___x_1613_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37));
lean_inc(v___x_1579_);
v___x_1614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1579_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40));
lean_inc_ref_n(v___x_1584_, 2);
lean_inc(v___x_1579_);
v___x_1616_ = l_Lean_Syntax_node2(v___x_1579_, v___x_1615_, v___x_1584_, v___x_1584_);
lean_inc_ref(v___x_1584_);
lean_inc(v___x_1579_);
v___x_1617_ = l_Lean_Syntax_node4(v___x_1579_, v___x_1612_, v___x_1614_, v_body_1499_, v___x_1616_, v___x_1584_);
lean_inc(v___x_1579_);
v___x_1618_ = l_Lean_Syntax_node5(v___x_1579_, v___x_1591_, v___x_1593_, v___x_1596_, v___x_1611_, v___x_1617_, v___x_1584_);
v___x_1619_ = l_Lean_Syntax_node2(v___x_1579_, v___x_1580_, v___x_1590_, v___x_1618_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1619_);
v___x_1621_ = v___x_1494_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1490_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec_ref(v_ctx_1475_);
return v___x_1491_;
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec_ref(v_ctx_1475_);
v_a_1643_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1489_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1489_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkAuxFunction___boxed(lean_object* v_ctx_1651_, lean_object* v_i_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction(v_ctx_1651_, v_i_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_i_1652_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(lean_object* v_upperBound_1661_, lean_object* v_ctx_1662_, lean_object* v_a_1663_, lean_object* v_b_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
uint8_t v___x_1672_; 
v___x_1672_ = lean_nat_dec_lt(v_a_1663_, v_upperBound_1661_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; 
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v_a_1663_);
lean_dec_ref(v_ctx_1662_);
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_b_1664_);
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; 
lean_inc(v___y_1670_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1665_);
lean_inc_ref(v_ctx_1662_);
v___x_1674_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction(v_ctx_1662_, v_a_1663_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref(v___x_1674_);
v___x_1676_ = lean_array_push(v_b_1664_, v_a_1675_);
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = lean_nat_add(v_a_1663_, v___x_1677_);
lean_dec(v_a_1663_);
v_a_1663_ = v___x_1678_;
v_b_1664_ = v___x_1676_;
goto _start;
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec_ref(v_b_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_ctx_1662_);
v_a_1680_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1674_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1674_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg___boxed(lean_object* v_upperBound_1688_, lean_object* v_ctx_1689_, lean_object* v_a_1690_, lean_object* v_b_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v_upperBound_1688_, v_ctx_1689_, v_a_1690_, v_b_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v_upperBound_1688_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs(lean_object* v_ctx_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_typeInfos_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v_auxDefs_1718_; lean_object* v___x_1719_; 
v_typeInfos_1715_ = lean_ctor_get(v_ctx_1707_, 1);
v___x_1716_ = lean_array_get_size(v_typeInfos_1715_);
v___x_1717_ = lean_unsigned_to_nat(0u);
v_auxDefs_1718_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___closed__1));
lean_inc_ref(v_a_1712_);
v___x_1719_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v___x_1716_, v_ctx_1707_, v___x_1717_, v_auxDefs_1718_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1740_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1740_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1740_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v_ref_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v_ref_1724_ = lean_ctor_get(v_a_1712_, 5);
lean_inc(v_ref_1724_);
lean_dec_ref(v_a_1712_);
v___x_1725_ = 0;
v___x_1726_ = l_Lean_SourceInfo_fromRef(v_ref_1724_, v___x_1725_);
lean_dec(v_ref_1724_);
v___x_1727_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0));
v___x_1728_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1));
lean_inc(v___x_1726_);
v___x_1729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1726_);
lean_ctor_set(v___x_1729_, 1, v___x_1727_);
v___x_1730_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__13));
v___x_1731_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__1___closed__3);
v___x_1732_ = l_Array_append___redArg(v___x_1731_, v_a_1720_);
lean_dec(v_a_1720_);
lean_inc(v___x_1726_);
v___x_1733_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1726_);
lean_ctor_set(v___x_1733_, 1, v___x_1730_);
lean_ctor_set(v___x_1733_, 2, v___x_1732_);
v___x_1734_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2));
lean_inc(v___x_1726_);
v___x_1735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1726_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = l_Lean_Syntax_node3(v___x_1726_, v___x_1728_, v___x_1729_, v___x_1733_, v___x_1735_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1736_);
v___x_1738_ = v___x_1722_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec_ref(v_a_1712_);
v_a_1741_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1719_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1719_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashFuncs___boxed(lean_object* v_ctx_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs(v_ctx_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0(lean_object* v_upperBound_1758_, lean_object* v_ctx_1759_, lean_object* v_inst_1760_, lean_object* v_R_1761_, lean_object* v_a_1762_, lean_object* v_b_1763_, lean_object* v_c_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v_upperBound_1758_, v_ctx_1759_, v_a_1762_, v_b_1763_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___boxed(lean_object* v_upperBound_1773_, lean_object* v_ctx_1774_, lean_object* v_inst_1775_, lean_object* v_R_1776_, lean_object* v_a_1777_, lean_object* v_b_1778_, lean_object* v_c_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0(v_upperBound_1773_, v_ctx_1774_, v_inst_1775_, v_R_1776_, v_a_1777_, v_b_1778_, v_c_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v_upperBound_1773_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg(lean_object* v_cls_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_options_1794_; uint8_t v_hasTrace_1795_; 
v_options_1794_ = lean_ctor_get(v___y_1792_, 2);
v_hasTrace_1795_ = lean_ctor_get_uint8(v_options_1794_, sizeof(void*)*1);
if (v_hasTrace_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v_cls_1791_);
v___x_1796_ = lean_box(v_hasTrace_1795_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
else
{
lean_object* v_inheritedTraceOptions_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_inheritedTraceOptions_1798_ = lean_ctor_get(v___y_1792_, 13);
v___x_1799_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg___closed__1));
v___x_1800_ = l_Lean_Name_append(v___x_1799_, v_cls_1791_);
v___x_1801_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1798_, v_options_1794_, v___x_1800_);
lean_dec(v___x_1800_);
v___x_1802_ = lean_box(v___x_1801_);
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg___boxed(lean_object* v_cls_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg(v_cls_1804_, v___y_1805_);
lean_dec_ref(v___y_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0(lean_object* v_cls_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg(v_cls_1808_, v___y_1813_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___boxed(lean_object* v_cls_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0(v_cls_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1(lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
if (lean_obj_tag(v_a_1826_) == 0)
{
lean_object* v___x_1828_; 
v___x_1828_ = l_List_reverse___redArg(v_a_1827_);
return v___x_1828_;
}
else
{
lean_object* v_head_1829_; lean_object* v_tail_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1839_; 
v_head_1829_ = lean_ctor_get(v_a_1826_, 0);
v_tail_1830_ = lean_ctor_get(v_a_1826_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_a_1826_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1832_ = v_a_1826_;
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_tail_1830_);
lean_inc(v_head_1829_);
lean_dec(v_a_1826_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1834_ = l_Lean_MessageData_ofSyntax(v_head_1829_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v_a_1827_);
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1836_ = v___x_1832_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_a_1827_);
v___x_1836_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
v_a_1826_ = v_tail_1830_;
v_a_1827_ = v___x_1836_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1840_; double v___x_1841_; 
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = lean_float_of_nat(v___x_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg(lean_object* v_cls_1844_, lean_object* v_msg_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_ref_1851_; lean_object* v___x_1852_; lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1897_; 
v_ref_1851_ = lean_ctor_get(v___y_1848_, 5);
v___x_1852_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msg_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1897_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1897_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v_traceState_1858_; lean_object* v_env_1859_; lean_object* v_nextMacroScope_1860_; lean_object* v_ngen_1861_; lean_object* v_auxDeclNGen_1862_; lean_object* v_cache_1863_; lean_object* v_messages_1864_; lean_object* v_infoState_1865_; lean_object* v_snapshotTasks_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1896_; 
v___x_1857_ = lean_st_ref_take(v___y_1849_);
v_traceState_1858_ = lean_ctor_get(v___x_1857_, 4);
v_env_1859_ = lean_ctor_get(v___x_1857_, 0);
v_nextMacroScope_1860_ = lean_ctor_get(v___x_1857_, 1);
v_ngen_1861_ = lean_ctor_get(v___x_1857_, 2);
v_auxDeclNGen_1862_ = lean_ctor_get(v___x_1857_, 3);
v_cache_1863_ = lean_ctor_get(v___x_1857_, 5);
v_messages_1864_ = lean_ctor_get(v___x_1857_, 6);
v_infoState_1865_ = lean_ctor_get(v___x_1857_, 7);
v_snapshotTasks_1866_ = lean_ctor_get(v___x_1857_, 8);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1868_ = v___x_1857_;
v_isShared_1869_ = v_isSharedCheck_1896_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_snapshotTasks_1866_);
lean_inc(v_infoState_1865_);
lean_inc(v_messages_1864_);
lean_inc(v_cache_1863_);
lean_inc(v_traceState_1858_);
lean_inc(v_auxDeclNGen_1862_);
lean_inc(v_ngen_1861_);
lean_inc(v_nextMacroScope_1860_);
lean_inc(v_env_1859_);
lean_dec(v___x_1857_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1896_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
uint64_t v_tid_1870_; lean_object* v_traces_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1895_; 
v_tid_1870_ = lean_ctor_get_uint64(v_traceState_1858_, sizeof(void*)*1);
v_traces_1871_ = lean_ctor_get(v_traceState_1858_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_traceState_1858_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1873_ = v_traceState_1858_;
v_isShared_1874_ = v_isSharedCheck_1895_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_traces_1871_);
lean_dec(v_traceState_1858_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1895_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; double v___x_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___closed__0);
v___x_1877_ = 0;
v___x_1878_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__21));
v___x_1879_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1879_, 0, v_cls_1844_);
lean_ctor_set(v___x_1879_, 1, v___x_1875_);
lean_ctor_set(v___x_1879_, 2, v___x_1878_);
lean_ctor_set_float(v___x_1879_, sizeof(void*)*3, v___x_1876_);
lean_ctor_set_float(v___x_1879_, sizeof(void*)*3 + 8, v___x_1876_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*3 + 16, v___x_1877_);
v___x_1880_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___closed__1));
v___x_1881_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v_a_1853_);
lean_ctor_set(v___x_1881_, 2, v___x_1880_);
lean_inc(v_ref_1851_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v_ref_1851_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l_Lean_PersistentArray_push___redArg(v_traces_1871_, v___x_1882_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1883_);
v___x_1885_ = v___x_1873_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1883_);
lean_ctor_set_uint64(v_reuseFailAlloc_1894_, sizeof(void*)*1, v_tid_1870_);
v___x_1885_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 4, v___x_1885_);
v___x_1887_ = v___x_1868_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_env_1859_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_nextMacroScope_1860_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_ngen_1861_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_auxDeclNGen_1862_);
lean_ctor_set(v_reuseFailAlloc_1893_, 4, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1893_, 5, v_cache_1863_);
lean_ctor_set(v_reuseFailAlloc_1893_, 6, v_messages_1864_);
lean_ctor_set(v_reuseFailAlloc_1893_, 7, v_infoState_1865_);
lean_ctor_set(v_reuseFailAlloc_1893_, 8, v_snapshotTasks_1866_);
v___x_1887_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1888_ = lean_st_ref_set(v___y_1849_, v___x_1887_);
v___x_1889_ = lean_box(0);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1889_);
v___x_1891_ = v___x_1855_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg___boxed(lean_object* v_cls_1898_, lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg(v_cls_1898_, v_msg_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2));
v___x_1913_ = l_Lean_stringToMessageData(v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds(lean_object* v_declName_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1922_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1));
v___x_1923_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___redArg___closed__39));
v___x_1924_ = 1;
lean_inc(v_a_1920_);
lean_inc_ref(v_a_1919_);
lean_inc(v_a_1918_);
lean_inc_ref(v_a_1917_);
lean_inc(v_a_1916_);
lean_inc_ref(v_a_1915_);
lean_inc(v_declName_1914_);
v___x_1925_ = l_Lean_Elab_Deriving_mkContext(v___x_1922_, v___x_1923_, v_declName_1914_, v___x_1924_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1925_);
lean_inc(v_a_1920_);
lean_inc_ref(v_a_1919_);
lean_inc(v_a_1918_);
lean_inc_ref(v_a_1917_);
lean_inc(v_a_1916_);
lean_inc_ref(v_a_1915_);
lean_inc(v_a_1926_);
v___x_1927_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs(v_a_1926_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = lean_unsigned_to_nat(1u);
v___x_1930_ = lean_mk_empty_array_with_capacity(v___x_1929_);
lean_inc_ref(v___x_1930_);
v___x_1931_ = lean_array_push(v___x_1930_, v_declName_1914_);
lean_inc(v_a_1920_);
lean_inc_ref(v_a_1919_);
lean_inc(v_a_1918_);
lean_inc_ref(v_a_1917_);
v___x_1932_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_1926_, v___x_1922_, v___x_1931_, v___x_1924_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
lean_dec_ref(v___x_1931_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1969_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1));
v___x_1935_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0___redArg(v___x_1934_, v_a_1919_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1969_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1969_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1940_ = lean_array_push(v___x_1930_, v_a_1928_);
v___x_1941_ = l_Array_append___redArg(v___x_1940_, v_a_1933_);
lean_dec(v_a_1933_);
v___x_1942_ = lean_unbox(v_a_1936_);
lean_dec(v_a_1936_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1944_; 
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1941_);
v___x_1944_ = v___x_1938_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1941_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
else
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_del_object(v___x_1938_);
v___x_1946_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3);
lean_inc_ref(v___x_1941_);
v___x_1947_ = lean_array_to_list(v___x_1941_);
v___x_1948_ = lean_box(0);
v___x_1949_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1(v___x_1947_, v___x_1948_);
v___x_1950_ = l_Lean_MessageData_ofList(v___x_1949_);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1946_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg(v___x_1934_, v___x_1951_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v___x_1952_, 0);
lean_dec(v_unused_1960_);
v___x_1954_ = v___x_1952_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_dec(v___x_1952_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1941_);
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1941_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v___x_1941_);
v_a_1961_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1952_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1952_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v___x_1930_);
lean_dec(v_a_1928_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
v_a_1970_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1932_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1932_);
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
lean_dec(v_a_1926_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_declName_1914_);
v_a_1978_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1927_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1927_);
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
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_declName_1914_);
v_a_1986_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1925_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1925_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___boxed(lean_object* v_declName_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds(v_declName_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2(lean_object* v_cls_2003_, lean_object* v_msg_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___redArg(v_cls_2003_, v_msg_2004_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2___boxed(lean_object* v_cls_2013_, lean_object* v_msg_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__2(v_cls_2013_, v_msg_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(lean_object* v_declName_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; lean_object* v_env_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2026_ = lean_st_ref_get(v___y_2024_);
v_env_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc_ref(v_env_2027_);
lean_dec(v___x_2026_);
v___x_2028_ = l_Lean_isInductiveCore(v_env_2027_, v_declName_2023_);
v___x_2029_ = lean_box(v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg___boxed(lean_object* v_declName_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(v_declName_2031_, v___y_2032_);
lean_dec(v___y_2032_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0(lean_object* v_declName_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(v_declName_2035_, v___y_2037_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___boxed(lean_object* v_declName_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0(v_declName_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0(uint8_t v_____do__lift_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
if (v_____do__lift_2045_ == 0)
{
uint8_t v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = 1;
v___x_2050_ = lean_box(v___x_2049_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
else
{
uint8_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = 0;
v___x_2053_ = lean_box(v___x_2052_);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0___boxed(lean_object* v_____do__lift_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
uint8_t v_____do__lift_4301__boxed_2059_; lean_object* v_res_2060_; 
v_____do__lift_4301__boxed_2059_ = lean_unbox(v_____do__lift_2055_);
v_res_2060_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0(v_____do__lift_4301__boxed_2059_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(lean_object* v_as_2061_, size_t v_i_2062_, size_t v_stop_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
uint8_t v___x_2067_; 
v___x_2067_ = lean_usize_dec_eq(v_i_2062_, v_stop_2063_);
if (v___x_2067_ == 0)
{
uint8_t v___x_2068_; uint8_t v_a_2070_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2068_ = 1;
v___x_2076_ = lean_array_uget_borrowed(v_as_2061_, v_i_2062_);
lean_inc(v___x_2076_);
v___x_2077_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(v___x_2076_, v___y_2065_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2087_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2087_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2087_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_unbox(v_a_2078_);
lean_dec(v_a_2078_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_box(v___x_2068_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2083_);
v___x_2085_ = v___x_2080_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
else
{
lean_del_object(v___x_2080_);
v_a_2070_ = v___x_2067_;
goto v___jp_2069_;
}
}
}
else
{
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2088_; uint8_t v___x_2089_; 
v_a_2088_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2088_);
lean_dec_ref(v___x_2077_);
v___x_2089_ = lean_unbox(v_a_2088_);
lean_dec(v_a_2088_);
v_a_2070_ = v___x_2089_;
goto v___jp_2069_;
}
else
{
return v___x_2077_;
}
}
v___jp_2069_:
{
if (v_a_2070_ == 0)
{
size_t v___x_2071_; size_t v___x_2072_; 
v___x_2071_ = ((size_t)1ULL);
v___x_2072_ = lean_usize_add(v_i_2062_, v___x_2071_);
v_i_2062_ = v___x_2072_;
goto _start;
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_box(v___x_2068_);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
}
}
else
{
uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = 0;
v___x_2091_ = lean_box(v___x_2090_);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3___boxed(lean_object* v_as_2093_, lean_object* v_i_2094_, lean_object* v_stop_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
size_t v_i_boxed_2099_; size_t v_stop_boxed_2100_; lean_object* v_res_2101_; 
v_i_boxed_2099_ = lean_unbox_usize(v_i_2094_);
lean_dec(v_i_2094_);
v_stop_boxed_2100_ = lean_unbox_usize(v_stop_2095_);
lean_dec(v_stop_2095_);
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(v_as_2093_, v_i_boxed_2099_, v_stop_boxed_2100_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec_ref(v_as_2093_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(lean_object* v_as_2102_, size_t v_i_2103_, size_t v_stop_2104_, lean_object* v_b_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v___x_2109_; 
v___x_2109_ = lean_usize_dec_eq(v_i_2103_, v_stop_2104_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_array_uget_borrowed(v_as_2102_, v_i_2103_);
lean_inc(v___y_2107_);
lean_inc_ref(v___y_2106_);
lean_inc(v___x_2110_);
v___x_2111_ = l_Lean_Elab_Command_elabCommand(v___x_2110_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; size_t v___x_2113_; size_t v___x_2114_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref(v___x_2111_);
v___x_2113_ = ((size_t)1ULL);
v___x_2114_ = lean_usize_add(v_i_2103_, v___x_2113_);
v_i_2103_ = v___x_2114_;
v_b_2105_ = v_a_2112_;
goto _start;
}
else
{
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v___x_2111_;
}
}
else
{
lean_object* v___x_2116_; 
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v_b_2105_);
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1___boxed(lean_object* v_as_2117_, lean_object* v_i_2118_, lean_object* v_stop_2119_, lean_object* v_b_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
size_t v_i_boxed_2124_; size_t v_stop_boxed_2125_; lean_object* v_res_2126_; 
v_i_boxed_2124_ = lean_unbox_usize(v_i_2118_);
lean_dec(v_i_2118_);
v_stop_boxed_2125_ = lean_unbox_usize(v_stop_2119_);
lean_dec(v_stop_2119_);
v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_as_2117_, v_i_boxed_2124_, v_stop_boxed_2125_, v_b_2120_, v___y_2121_, v___y_2122_);
lean_dec_ref(v_as_2117_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0(lean_object* v___x_2127_, lean_object* v___x_2128_, lean_object* v___x_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; 
lean_inc_ref(v___y_2130_);
v___x_2133_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_2127_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2153_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2153_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2153_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = lean_array_get_size(v_a_2134_);
v___x_2139_ = lean_nat_dec_lt(v___x_2128_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2141_; 
lean_dec(v_a_2134_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2129_);
v___x_2141_ = v___x_2136_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2129_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
else
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_nat_dec_le(v___x_2138_, v___x_2138_);
if (v___x_2143_ == 0)
{
if (v___x_2139_ == 0)
{
lean_object* v___x_2145_; 
lean_dec(v_a_2134_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2129_);
v___x_2145_ = v___x_2136_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2129_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
else
{
size_t v___x_2147_; size_t v___x_2148_; lean_object* v___x_2149_; 
lean_del_object(v___x_2136_);
v___x_2147_ = ((size_t)0ULL);
v___x_2148_ = lean_usize_of_nat(v___x_2138_);
v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_a_2134_, v___x_2147_, v___x_2148_, v___x_2129_, v___y_2130_, v___y_2131_);
lean_dec(v_a_2134_);
return v___x_2149_;
}
}
else
{
size_t v___x_2150_; size_t v___x_2151_; lean_object* v___x_2152_; 
lean_del_object(v___x_2136_);
v___x_2150_ = ((size_t)0ULL);
v___x_2151_ = lean_usize_of_nat(v___x_2138_);
v___x_2152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_a_2134_, v___x_2150_, v___x_2151_, v___x_2129_, v___y_2130_, v___y_2131_);
lean_dec(v_a_2134_);
return v___x_2152_;
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
v_a_2154_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2133_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2133_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0___boxed(lean_object* v___x_2162_, lean_object* v___x_2163_, lean_object* v___x_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0(v___x_2162_, v___x_2163_, v___x_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___x_2163_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(lean_object* v_as_2169_, size_t v_sz_2170_, size_t v_i_2171_, lean_object* v_b_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_usize_dec_lt(v_i_2171_, v_sz_2170_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; 
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_b_2172_);
return v___x_2177_;
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v_a_2180_; lean_object* v___x_2181_; lean_object* v___f_2182_; lean_object* v___x_2183_; 
v___x_2178_ = lean_unsigned_to_nat(0u);
v___x_2179_ = lean_box(0);
v_a_2180_ = lean_array_uget_borrowed(v_as_2169_, v_i_2171_);
lean_inc(v_a_2180_);
v___x_2181_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_2181_, 0, v_a_2180_);
v___f_2182_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2182_, 0, v___x_2181_);
lean_closure_set(v___f_2182_, 1, v___x_2178_);
lean_closure_set(v___f_2182_, 2, v___x_2179_);
lean_inc(v___y_2174_);
lean_inc_ref(v___y_2173_);
lean_inc(v_a_2180_);
v___x_2183_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_2180_, v___f_2182_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2183_) == 0)
{
size_t v___x_2184_; size_t v___x_2185_; 
lean_dec_ref(v___x_2183_);
v___x_2184_ = ((size_t)1ULL);
v___x_2185_ = lean_usize_add(v_i_2171_, v___x_2184_);
v_i_2171_ = v___x_2185_;
v_b_2172_ = v___x_2179_;
goto _start;
}
else
{
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
return v___x_2183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___boxed(lean_object* v_as_2187_, lean_object* v_sz_2188_, lean_object* v_i_2189_, lean_object* v_b_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
size_t v_sz_boxed_2194_; size_t v_i_boxed_2195_; lean_object* v_res_2196_; 
v_sz_boxed_2194_ = lean_unbox_usize(v_sz_2188_);
lean_dec(v_sz_2188_);
v_i_boxed_2195_ = lean_unbox_usize(v_i_2189_);
lean_dec(v_i_2189_);
v_res_2196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(v_as_2187_, v_sz_boxed_2194_, v_i_boxed_2195_, v_b_2190_, v___y_2191_, v___y_2192_);
lean_dec_ref(v_as_2187_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1(lean_object* v_declNames_2197_, lean_object* v___x_2198_, lean_object* v___x_2199_, lean_object* v___f_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___y_2228_; uint8_t v___x_2231_; 
v___x_2231_ = lean_nat_dec_lt(v___x_2198_, v___x_2199_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = lean_box(v___x_2231_);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
v___x_2233_ = lean_apply_4(v___f_2200_, v___x_2232_, v___y_2201_, v___y_2202_, lean_box(0));
v___y_2228_ = v___x_2233_;
goto v___jp_2227_;
}
else
{
if (v___x_2231_ == 0)
{
lean_dec_ref(v___f_2200_);
goto v___jp_2204_;
}
else
{
size_t v___x_2234_; size_t v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = lean_usize_of_nat(v___x_2199_);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(v_declNames_2197_, v___x_2234_, v___x_2235_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2238_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref(v___x_2236_);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
v___x_2238_ = lean_apply_4(v___f_2200_, v_a_2237_, v___y_2201_, v___y_2202_, lean_box(0));
v___y_2228_ = v___x_2238_;
goto v___jp_2227_;
}
else
{
lean_dec_ref(v___f_2200_);
v___y_2228_ = v___x_2236_;
goto v___jp_2227_;
}
}
}
v___jp_2204_:
{
lean_object* v___x_2205_; size_t v_sz_2206_; size_t v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = lean_box(0);
v_sz_2206_ = lean_array_size(v_declNames_2197_);
v___x_2207_ = ((size_t)0ULL);
v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(v_declNames_2197_, v_sz_2206_, v___x_2207_, v___x_2205_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2217_; 
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; 
v_unused_2218_ = lean_ctor_get(v___x_2208_, 0);
lean_dec(v_unused_2218_);
v___x_2210_ = v___x_2208_;
v_isShared_2211_ = v_isSharedCheck_2217_;
goto v_resetjp_2209_;
}
else
{
lean_dec(v___x_2208_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2217_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
uint8_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2212_ = 1;
v___x_2213_ = lean_box(v___x_2212_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2213_);
v___x_2215_ = v___x_2210_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
v_a_2219_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2208_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2208_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
v___jp_2227_:
{
if (lean_obj_tag(v___y_2228_) == 0)
{
lean_object* v_a_2229_; uint8_t v___x_2230_; 
v_a_2229_ = lean_ctor_get(v___y_2228_, 0);
v___x_2230_ = lean_unbox(v_a_2229_);
if (v___x_2230_ == 0)
{
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v___y_2228_;
}
else
{
lean_dec_ref(v___y_2228_);
goto v___jp_2204_;
}
}
else
{
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v___y_2228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1___boxed(lean_object* v_declNames_2239_, lean_object* v___x_2240_, lean_object* v___x_2241_, lean_object* v___f_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1(v_declNames_2239_, v___x_2240_, v___x_2241_, v___f_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___x_2241_);
lean_dec(v___x_2240_);
lean_dec_ref(v_declNames_2239_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(lean_object* v___y_2247_, uint8_t v_isExporting_2248_, lean_object* v_a_x3f_2249_){
_start:
{
lean_object* v___x_2251_; lean_object* v_env_2252_; lean_object* v_messages_2253_; lean_object* v_scopes_2254_; lean_object* v_usedQuotCtxts_2255_; lean_object* v_nextMacroScope_2256_; lean_object* v_maxRecDepth_2257_; lean_object* v_ngen_2258_; lean_object* v_auxDeclNGen_2259_; lean_object* v_infoState_2260_; lean_object* v_traceState_2261_; lean_object* v_snapshotTasks_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2273_; 
v___x_2251_ = lean_st_ref_take(v___y_2247_);
v_env_2252_ = lean_ctor_get(v___x_2251_, 0);
v_messages_2253_ = lean_ctor_get(v___x_2251_, 1);
v_scopes_2254_ = lean_ctor_get(v___x_2251_, 2);
v_usedQuotCtxts_2255_ = lean_ctor_get(v___x_2251_, 3);
v_nextMacroScope_2256_ = lean_ctor_get(v___x_2251_, 4);
v_maxRecDepth_2257_ = lean_ctor_get(v___x_2251_, 5);
v_ngen_2258_ = lean_ctor_get(v___x_2251_, 6);
v_auxDeclNGen_2259_ = lean_ctor_get(v___x_2251_, 7);
v_infoState_2260_ = lean_ctor_get(v___x_2251_, 8);
v_traceState_2261_ = lean_ctor_get(v___x_2251_, 9);
v_snapshotTasks_2262_ = lean_ctor_get(v___x_2251_, 10);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2264_ = v___x_2251_;
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_snapshotTasks_2262_);
lean_inc(v_traceState_2261_);
lean_inc(v_infoState_2260_);
lean_inc(v_auxDeclNGen_2259_);
lean_inc(v_ngen_2258_);
lean_inc(v_maxRecDepth_2257_);
lean_inc(v_nextMacroScope_2256_);
lean_inc(v_usedQuotCtxts_2255_);
lean_inc(v_scopes_2254_);
lean_inc(v_messages_2253_);
lean_inc(v_env_2252_);
lean_dec(v___x_2251_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2266_ = l_Lean_Environment_setExporting(v_env_2252_, v_isExporting_2248_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v_messages_2253_);
lean_ctor_set(v_reuseFailAlloc_2272_, 2, v_scopes_2254_);
lean_ctor_set(v_reuseFailAlloc_2272_, 3, v_usedQuotCtxts_2255_);
lean_ctor_set(v_reuseFailAlloc_2272_, 4, v_nextMacroScope_2256_);
lean_ctor_set(v_reuseFailAlloc_2272_, 5, v_maxRecDepth_2257_);
lean_ctor_set(v_reuseFailAlloc_2272_, 6, v_ngen_2258_);
lean_ctor_set(v_reuseFailAlloc_2272_, 7, v_auxDeclNGen_2259_);
lean_ctor_set(v_reuseFailAlloc_2272_, 8, v_infoState_2260_);
lean_ctor_set(v_reuseFailAlloc_2272_, 9, v_traceState_2261_);
lean_ctor_set(v_reuseFailAlloc_2272_, 10, v_snapshotTasks_2262_);
v___x_2268_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = lean_st_ref_set(v___y_2247_, v___x_2268_);
v___x_2270_ = lean_box(0);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
return v___x_2271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v___y_2274_, lean_object* v_isExporting_2275_, lean_object* v_a_x3f_2276_, lean_object* v___y_2277_){
_start:
{
uint8_t v_isExporting_boxed_2278_; lean_object* v_res_2279_; 
v_isExporting_boxed_2278_ = lean_unbox(v_isExporting_2275_);
v_res_2279_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_2274_, v_isExporting_boxed_2278_, v_a_x3f_2276_);
lean_dec(v_a_x3f_2276_);
lean_dec(v___y_2274_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(lean_object* v_x_2280_, uint8_t v_isExporting_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v_env_2286_; uint8_t v_isExporting_2287_; lean_object* v___x_2288_; lean_object* v_env_2289_; lean_object* v_messages_2290_; lean_object* v_scopes_2291_; lean_object* v_usedQuotCtxts_2292_; lean_object* v_nextMacroScope_2293_; lean_object* v_maxRecDepth_2294_; lean_object* v_ngen_2295_; lean_object* v_auxDeclNGen_2296_; lean_object* v_infoState_2297_; lean_object* v_traceState_2298_; lean_object* v_snapshotTasks_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2337_; 
v___x_2285_ = lean_st_ref_get(v___y_2283_);
v_env_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc_ref(v_env_2286_);
lean_dec(v___x_2285_);
v_isExporting_2287_ = lean_ctor_get_uint8(v_env_2286_, sizeof(void*)*8);
lean_dec_ref(v_env_2286_);
v___x_2288_ = lean_st_ref_take(v___y_2283_);
v_env_2289_ = lean_ctor_get(v___x_2288_, 0);
v_messages_2290_ = lean_ctor_get(v___x_2288_, 1);
v_scopes_2291_ = lean_ctor_get(v___x_2288_, 2);
v_usedQuotCtxts_2292_ = lean_ctor_get(v___x_2288_, 3);
v_nextMacroScope_2293_ = lean_ctor_get(v___x_2288_, 4);
v_maxRecDepth_2294_ = lean_ctor_get(v___x_2288_, 5);
v_ngen_2295_ = lean_ctor_get(v___x_2288_, 6);
v_auxDeclNGen_2296_ = lean_ctor_get(v___x_2288_, 7);
v_infoState_2297_ = lean_ctor_get(v___x_2288_, 8);
v_traceState_2298_ = lean_ctor_get(v___x_2288_, 9);
v_snapshotTasks_2299_ = lean_ctor_get(v___x_2288_, 10);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2301_ = v___x_2288_;
v_isShared_2302_ = v_isSharedCheck_2337_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_snapshotTasks_2299_);
lean_inc(v_traceState_2298_);
lean_inc(v_infoState_2297_);
lean_inc(v_auxDeclNGen_2296_);
lean_inc(v_ngen_2295_);
lean_inc(v_maxRecDepth_2294_);
lean_inc(v_nextMacroScope_2293_);
lean_inc(v_usedQuotCtxts_2292_);
lean_inc(v_scopes_2291_);
lean_inc(v_messages_2290_);
lean_inc(v_env_2289_);
lean_dec(v___x_2288_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2337_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2303_ = l_Lean_Environment_setExporting(v_env_2289_, v_isExporting_2281_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2303_);
v___x_2305_ = v___x_2301_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_messages_2290_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_scopes_2291_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v_usedQuotCtxts_2292_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v_nextMacroScope_2293_);
lean_ctor_set(v_reuseFailAlloc_2336_, 5, v_maxRecDepth_2294_);
lean_ctor_set(v_reuseFailAlloc_2336_, 6, v_ngen_2295_);
lean_ctor_set(v_reuseFailAlloc_2336_, 7, v_auxDeclNGen_2296_);
lean_ctor_set(v_reuseFailAlloc_2336_, 8, v_infoState_2297_);
lean_ctor_set(v_reuseFailAlloc_2336_, 9, v_traceState_2298_);
lean_ctor_set(v_reuseFailAlloc_2336_, 10, v_snapshotTasks_2299_);
v___x_2305_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2306_; lean_object* v_r_2307_; 
v___x_2306_ = lean_st_ref_set(v___y_2283_, v___x_2305_);
lean_inc(v___y_2283_);
v_r_2307_ = lean_apply_3(v_x_2280_, v___y_2282_, v___y_2283_, lean_box(0));
if (lean_obj_tag(v_r_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2324_; 
v_a_2308_ = lean_ctor_get(v_r_2307_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_r_2307_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2310_ = v_r_2307_;
v_isShared_2311_ = v_isSharedCheck_2324_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v_r_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2324_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
lean_inc(v_a_2308_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 1);
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v___x_2314_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_2283_, v_isExporting_2287_, v___x_2313_);
lean_dec_ref(v___x_2313_);
lean_dec(v___y_2283_);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v___x_2314_, 0);
lean_dec(v_unused_2322_);
v___x_2316_ = v___x_2314_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_dec(v___x_2314_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v_a_2308_);
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2308_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
v_a_2325_ = lean_ctor_get(v_r_2307_, 0);
lean_inc(v_a_2325_);
lean_dec_ref(v_r_2307_);
v___x_2326_ = lean_box(0);
v___x_2327_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_2283_, v_isExporting_2287_, v___x_2326_);
lean_dec(v___y_2283_);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; 
v_unused_2335_ = lean_ctor_get(v___x_2327_, 0);
lean_dec(v_unused_2335_);
v___x_2329_ = v___x_2327_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_dec(v___x_2327_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
lean_ctor_set_tag(v___x_2329_, 1);
lean_ctor_set(v___x_2329_, 0, v_a_2325_);
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2325_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___boxed(lean_object* v_x_2338_, lean_object* v_isExporting_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
uint8_t v_isExporting_boxed_2343_; lean_object* v_res_2344_; 
v_isExporting_boxed_2343_ = lean_unbox(v_isExporting_2339_);
v_res_2344_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_2338_, v_isExporting_boxed_2343_, v___y_2340_, v___y_2341_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(lean_object* v_x_2345_, uint8_t v_when_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
if (v_when_2346_ == 0)
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_apply_3(v_x_2345_, v___y_2347_, v___y_2348_, lean_box(0));
return v___x_2350_;
}
else
{
uint8_t v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = 0;
v___x_2352_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_2345_, v___x_2351_, v___y_2347_, v___y_2348_);
return v___x_2352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg___boxed(lean_object* v_x_2353_, lean_object* v_when_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
uint8_t v_when_boxed_2358_; lean_object* v_res_2359_; 
v_when_boxed_2358_ = lean_unbox(v_when_2354_);
v_res_2359_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v_x_2353_, v_when_boxed_2358_, v___y_2355_, v___y_2356_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler(lean_object* v_declNames_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v___f_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___f_2368_; uint8_t v___x_2369_; lean_object* v___x_2370_; 
v___f_2365_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHandler___closed__0));
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = lean_array_get_size(v_declNames_2361_);
v___f_2368_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1___boxed), 7, 4);
lean_closure_set(v___f_2368_, 0, v_declNames_2361_);
lean_closure_set(v___f_2368_, 1, v___x_2366_);
lean_closure_set(v___f_2368_, 2, v___x_2367_);
lean_closure_set(v___f_2368_, 3, v___f_2365_);
v___x_2369_ = 1;
v___x_2370_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v___f_2368_, v___x_2369_, v_a_2362_, v_a_2363_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Hashable_mkHashableHandler___boxed(lean_object* v_declNames_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler(v_declNames_2371_, v_a_2372_, v_a_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4(lean_object* v_00_u03b1_2376_, lean_object* v_x_2377_, uint8_t v_isExporting_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_2377_, v_isExporting_2378_, v___y_2379_, v___y_2380_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___boxed(lean_object* v_00_u03b1_2383_, lean_object* v_x_2384_, lean_object* v_isExporting_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
uint8_t v_isExporting_boxed_2389_; lean_object* v_res_2390_; 
v_isExporting_boxed_2389_ = lean_unbox(v_isExporting_2385_);
v_res_2390_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4(v_00_u03b1_2383_, v_x_2384_, v_isExporting_boxed_2389_, v___y_2386_, v___y_2387_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4(lean_object* v_00_u03b1_2391_, lean_object* v_x_2392_, uint8_t v_when_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v_x_2392_, v_when_2393_, v___y_2394_, v___y_2395_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___boxed(lean_object* v_00_u03b1_2398_, lean_object* v_x_2399_, lean_object* v_when_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
uint8_t v_when_boxed_2404_; lean_object* v_res_2405_; 
v_when_boxed_2404_ = lean_unbox(v_when_2400_);
v_res_2405_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4(v_00_u03b1_2398_, v_x_2399_, v_when_boxed_2404_, v___y_2401_, v___y_2402_);
return v_res_2405_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = lean_unsigned_to_nat(4079464183u);
v___x_2459_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__19_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2460_ = l_Lean_Name_num___override(v___x_2459_, v___x_2458_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__21_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2463_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2464_ = l_Lean_Name_str___override(v___x_2463_, v___x_2462_);
return v___x_2464_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__23_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2467_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2468_ = l_Lean_Name_str___override(v___x_2467_, v___x_2466_);
return v___x_2468_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = lean_unsigned_to_nat(2u);
v___x_2470_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2471_ = l_Lean_Name_num___override(v___x_2470_, v___x_2469_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = ((lean_object*)(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1));
v___x_2474_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__0_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_));
v___x_2475_ = l_Lean_Elab_registerDerivingHandler(v___x_2473_, v___x_2474_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_dec_ref(v___x_2475_);
v___x_2476_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1));
v___x_2477_ = 0;
v___x_2478_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
v___x_2479_ = l_Lean_registerTraceClass(v___x_2476_, v___x_2477_, v___x_2478_);
return v___x_2479_;
}
else
{
return v___x_2475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2____boxed(lean_object* v_a_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_();
return v_res_2481_;
}
}
lean_object* runtime_initialize_Lean_Meta_Inductive(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
