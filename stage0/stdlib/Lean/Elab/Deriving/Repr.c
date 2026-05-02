// Lean compiler output
// Module: Lean.Elab.Deriving.Repr
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getBinderInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
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
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Repr"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 59, 131, 233, 62, 241, 250, 220)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prec"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value),LEAN_SCALAR_PTR_LITERAL(178, 133, 204, 73, 239, 123, 12, 87)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 163, 238, 151, 160, 85, 71, 16)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_++_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 69, 86, 178, 149, 48, 216, 23)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "++"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\" := \""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__7_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__9_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__9_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__11_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__12_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__13;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__14_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__15_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__16_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__16_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 44, 178, 157, 49, 38, 131, 220)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__16_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__16_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__17_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__18_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__19_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__19_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__20_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__21_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__22_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__22_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__22_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__23 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__23_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__24_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__24_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__24_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__24_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__25_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__26_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__23_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__26_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__27_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__20_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__27_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__28_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__17_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__28_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__29_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__30_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Format.group"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__32_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__33;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Format"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__35 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__35_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__36_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(199, 101, 149, 40, 211, 134, 215, 211)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__36_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__37_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__37_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(244, 69, 187, 229, 60, 74, 115, 66)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__37_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__38_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__37_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__39_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__40 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__40_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__38_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__40_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__41_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Format.nest"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__42_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__43;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "nest"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__44 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__44_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__45_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(8, 121, 197, 203, 165, 174, 61, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__45 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__45_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__46_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__46_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(179, 146, 214, 149, 195, 116, 102, 235)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__46 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__46_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__47 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__47_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__46_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__48 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__48_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__49 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__49_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__47_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__49_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__50 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__50_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "repr"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__51 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__51_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__52;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(248, 109, 138, 163, 21, 170, 71, 243)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__53 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__53_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__53_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__54 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__54_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__55 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__55_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__56 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__56_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__57_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__57_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__57_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__57 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__57_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__58 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__58_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\"_\""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__59 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__59_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\",\""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Format.line"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "line"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(20, 237, 177, 226, 131, 244, 212, 161)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 89, 162, 50, 159, 227, 59, 53)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__6_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__7_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__9_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Format.nil"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 110, 112, 1, 140, 132, 234, 227)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(38, 56, 177, 235, 80, 228, 131, 10)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Format.bracket"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bracket"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(174, 48, 2, 244, 180, 197, 18, 79)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(173, 181, 123, 51, 4, 114, 72, 159)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\"{ \""};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\" }\""};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "'deriving Repr' failed, unexpected number of fields in structure"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reprArg"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 167, 21, 149, 233, 224, 156, 221)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termMax_prec"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 118, 206, 137, 233, 43, 182)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "max_prec"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 42, 41, 58, 31, 42, 63)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 243, 205, 40, 12, 75, 164, 249)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Format.text"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Repr.addAppParen"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "addAppParen"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 59, 131, 233, 62, 241, 250, 220)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(81, 6, 140, 45, 150, 11, 23, 193)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__23_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__20_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__17_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≥_"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(58, 65, 30, 214, 7, 203, 184, 211)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ">="};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0_value;
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "no_expose"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value),LEAN_SCALAR_PTR_LITERAL(211, 61, 129, 110, 227, 154, 234, 3)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(224, 137, 43, 251, 2, 178, 60, 92)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 224, 49, 20, 188, 146, 89, 35)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(208, 160, 169, 100, 58, 75, 239, 18)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(169, 95, 81, 7, 4, 169, 73, 180)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(231, 58, 223, 30, 148, 240, 234, 38)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(225, 21, 194, 109, 33, 15, 109, 4)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 231, 73, 27, 250, 149, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 145, 209, 124, 47, 69, 201, 61)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 215, 65, 207, 88, 39, 128, 71)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(211, 53, 156, 16, 162, 242, 38, 216)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(69, 90, 211, 79, 166, 122, 95, 47)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(43, 134, 118, 68, 66, 204, 66, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 138, 48, 165, 232, 217, 168, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1829928117) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(125, 196, 216, 153, 78, 142, 253, 232)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 155, 187, 30, 146, 67, 38, 109)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 217, 197, 232, 108, 25, 15, 192)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(139, 0, 128, 151, 4, 60, 211, 133)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10));
v___x_19_ = l_String_toRawSubstring_x27(v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14));
v___x_25_ = l_String_toRawSubstring_x27(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Array_mkArray0(lean_box(0));
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader(lean_object* v_indVal_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = l_Lean_Elab_Deriving_mkHeader(v___x_52_, v___x_53_, v_indVal_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_102_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_102_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_102_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_102_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v_ref_59_; lean_object* v_quotContext_60_; lean_object* v_currMacroScope_61_; uint8_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v_binders_84_; lean_object* v_argNames_85_; lean_object* v_targetNames_86_; lean_object* v_targetType_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_101_; 
v_ref_59_ = lean_ctor_get(v_a_49_, 5);
v_quotContext_60_ = lean_ctor_get(v_a_49_, 10);
v_currMacroScope_61_ = lean_ctor_get(v_a_49_, 11);
v___x_62_ = 0;
v___x_63_ = l_Lean_SourceInfo_fromRef(v_ref_59_, v___x_62_);
v___x_64_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6));
v___x_65_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7));
lean_inc_n(v___x_63_, 7);
v___x_66_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_63_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_68_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11);
v___x_69_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12));
lean_inc_n(v_currMacroScope_61_, 2);
lean_inc_n(v_quotContext_60_, 2);
v___x_70_ = l_Lean_addMacroScope(v_quotContext_60_, v___x_69_, v_currMacroScope_61_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_72_, 0, v___x_63_);
lean_ctor_set(v___x_72_, 1, v___x_68_);
lean_ctor_set(v___x_72_, 2, v___x_70_);
lean_ctor_set(v___x_72_, 3, v___x_71_);
v___x_73_ = l_Lean_Syntax_node1(v___x_63_, v___x_67_, v___x_72_);
v___x_74_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13));
v___x_75_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_63_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15);
v___x_77_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16));
v___x_78_ = l_Lean_addMacroScope(v_quotContext_60_, v___x_77_, v_currMacroScope_61_);
v___x_79_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21));
v___x_80_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_80_, 0, v___x_63_);
lean_ctor_set(v___x_80_, 1, v___x_76_);
lean_ctor_set(v___x_80_, 2, v___x_78_);
lean_ctor_set(v___x_80_, 3, v___x_79_);
v___x_81_ = l_Lean_Syntax_node2(v___x_63_, v___x_67_, v___x_75_, v___x_80_);
v___x_82_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_83_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_83_, 0, v___x_63_);
lean_ctor_set(v___x_83_, 1, v___x_67_);
lean_ctor_set(v___x_83_, 2, v___x_82_);
v_binders_84_ = lean_ctor_get(v_a_55_, 0);
v_argNames_85_ = lean_ctor_get(v_a_55_, 1);
v_targetNames_86_ = lean_ctor_get(v_a_55_, 2);
v_targetType_87_ = lean_ctor_get(v_a_55_, 3);
v_isSharedCheck_101_ = !lean_is_exclusive(v_a_55_);
if (v_isSharedCheck_101_ == 0)
{
v___x_89_ = v_a_55_;
v_isShared_90_ = v_isSharedCheck_101_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_targetType_87_);
lean_inc(v_targetNames_86_);
lean_inc(v_argNames_85_);
lean_inc(v_binders_84_);
lean_dec(v_a_55_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_101_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_91_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23));
lean_inc(v___x_63_);
v___x_92_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_63_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = l_Lean_Syntax_node5(v___x_63_, v___x_64_, v___x_66_, v___x_73_, v___x_81_, v___x_83_, v___x_92_);
v___x_94_ = lean_array_push(v_binders_84_, v___x_93_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_94_);
v___x_96_ = v___x_89_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_argNames_85_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_targetNames_86_);
lean_ctor_set(v_reuseFailAlloc_100_, 3, v_targetType_87_);
v___x_96_ = v_reuseFailAlloc_100_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_98_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_96_);
v___x_98_ = v___x_57_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
else
{
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___boxed(lean_object* v_indVal_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Elab_Deriving_Repr_mkReprHeader(v_indVal_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___lam__0(lean_object* v_k_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v_b_115_, lean_object* v_c_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; 
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
lean_inc(v___y_118_);
lean_inc_ref(v___y_117_);
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
v___x_122_ = lean_apply_9(v_k_112_, v_b_115_, v_c_116_, v___y_113_, v___y_114_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, lean_box(0));
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___lam__0___boxed(lean_object* v_k_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v_b_126_, lean_object* v_c_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___lam__0(v_k_123_, v___y_124_, v___y_125_, v_b_126_, v_c_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(lean_object* v_type_134_, lean_object* v_k_135_, uint8_t v_cleanupAnnotations_136_, uint8_t v_whnfType_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___f_145_; lean_object* v___x_146_; 
lean_inc(v___y_139_);
lean_inc_ref(v___y_138_);
v___f_145_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_145_, 0, v_k_135_);
lean_closure_set(v___f_145_, 1, v___y_138_);
lean_closure_set(v___f_145_, 2, v___y_139_);
v___x_146_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_134_, v___f_145_, v_cleanupAnnotations_136_, v_whnfType_137_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_146_) == 0)
{
return v___x_146_;
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___boxed(lean_object* v_type_155_, lean_object* v_k_156_, lean_object* v_cleanupAnnotations_157_, lean_object* v_whnfType_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_166_; uint8_t v_whnfType_boxed_167_; lean_object* v_res_168_; 
v_cleanupAnnotations_boxed_166_ = lean_unbox(v_cleanupAnnotations_157_);
v_whnfType_boxed_167_ = lean_unbox(v_whnfType_158_);
v_res_168_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v_type_155_, v_k_156_, v_cleanupAnnotations_boxed_166_, v_whnfType_boxed_167_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(lean_object* v_00_u03b1_169_, lean_object* v_type_170_, lean_object* v_k_171_, uint8_t v_cleanupAnnotations_172_, uint8_t v_whnfType_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v_type_170_, v_k_171_, v_cleanupAnnotations_172_, v_whnfType_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___boxed(lean_object* v_00_u03b1_182_, lean_object* v_type_183_, lean_object* v_k_184_, lean_object* v_cleanupAnnotations_185_, lean_object* v_whnfType_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_194_; uint8_t v_whnfType_boxed_195_; lean_object* v_res_196_; 
v_cleanupAnnotations_boxed_194_ = lean_unbox(v_cleanupAnnotations_185_);
v_whnfType_boxed_195_ = lean_unbox(v_whnfType_186_);
v_res_196_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(v_00_u03b1_182_, v_type_183_, v_k_184_, v_cleanupAnnotations_boxed_194_, v_whnfType_boxed_195_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__3(lean_object* v_msgData_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; lean_object* v_env_204_; lean_object* v___x_205_; lean_object* v_mctx_206_; lean_object* v_lctx_207_; lean_object* v_options_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_203_ = lean_st_ref_get(v___y_201_);
v_env_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc_ref(v_env_204_);
lean_dec(v___x_203_);
v___x_205_ = lean_st_ref_get(v___y_199_);
v_mctx_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc_ref(v_mctx_206_);
lean_dec(v___x_205_);
v_lctx_207_ = lean_ctor_get(v___y_198_, 2);
v_options_208_ = lean_ctor_get(v___y_200_, 2);
lean_inc_ref(v_options_208_);
lean_inc_ref(v_lctx_207_);
v___x_209_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_209_, 0, v_env_204_);
lean_ctor_set(v___x_209_, 1, v_mctx_206_);
lean_ctor_set(v___x_209_, 2, v_lctx_207_);
lean_ctor_set(v___x_209_, 3, v_options_208_);
v___x_210_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v_msgData_197_);
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__3___boxed(lean_object* v_msgData_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__3(v_msgData_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_218_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__6(lean_object* v_opts_219_, lean_object* v_opt_220_){
_start:
{
lean_object* v_name_221_; lean_object* v_defValue_222_; lean_object* v_map_223_; lean_object* v___x_224_; 
v_name_221_ = lean_ctor_get(v_opt_220_, 0);
v_defValue_222_ = lean_ctor_get(v_opt_220_, 1);
v_map_223_ = lean_ctor_get(v_opts_219_, 0);
v___x_224_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_223_, v_name_221_);
if (lean_obj_tag(v___x_224_) == 0)
{
uint8_t v___x_225_; 
v___x_225_ = lean_unbox(v_defValue_222_);
return v___x_225_;
}
else
{
lean_object* v_val_226_; 
v_val_226_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_226_);
lean_dec_ref(v___x_224_);
if (lean_obj_tag(v_val_226_) == 1)
{
uint8_t v_v_227_; 
v_v_227_ = lean_ctor_get_uint8(v_val_226_, 0);
lean_dec_ref(v_val_226_);
return v_v_227_;
}
else
{
uint8_t v___x_228_; 
lean_dec(v_val_226_);
v___x_228_ = lean_unbox(v_defValue_222_);
return v___x_228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__6___boxed(lean_object* v_opts_229_, lean_object* v_opt_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__6(v_opts_229_, v_opt_230_);
lean_dec_ref(v_opt_230_);
lean_dec_ref(v_opts_229_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__0(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_box(1);
v___x_234_ = l_Lean_MessageData_ofFormat(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__3(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__2));
v___x_239_ = l_Lean_MessageData_ofFormat(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7(lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
return v_x_240_;
}
else
{
lean_object* v_head_242_; lean_object* v_tail_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_265_; 
v_head_242_ = lean_ctor_get(v_x_241_, 0);
v_tail_243_ = lean_ctor_get(v_x_241_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_x_241_);
if (v_isSharedCheck_265_ == 0)
{
v___x_245_ = v_x_241_;
v_isShared_246_ = v_isSharedCheck_265_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_tail_243_);
lean_inc(v_head_242_);
lean_dec(v_x_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_265_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_before_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_263_; 
v_before_247_ = lean_ctor_get(v_head_242_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v_head_242_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; 
v_unused_264_ = lean_ctor_get(v_head_242_, 1);
lean_dec(v_unused_264_);
v___x_249_ = v_head_242_;
v_isShared_250_ = v_isSharedCheck_263_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_before_247_);
lean_dec(v_head_242_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_263_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_251_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__0);
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 7);
lean_ctor_set(v___x_249_, 1, v___x_251_);
lean_ctor_set(v___x_249_, 0, v_x_240_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_x_240_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___x_251_);
v___x_253_ = v_reuseFailAlloc_262_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__3);
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 7);
lean_ctor_set(v___x_245_, 1, v___x_254_);
lean_ctor_set(v___x_245_, 0, v___x_253_);
v___x_256_ = v___x_245_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_254_);
v___x_256_ = v_reuseFailAlloc_261_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = l_Lean_MessageData_ofSyntax(v_before_247_);
v___x_258_ = l_Lean_indentD(v___x_257_);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_256_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v_x_240_ = v___x_259_;
v_x_241_ = v_tail_243_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__1));
v___x_270_ = l_Lean_MessageData_ofFormat(v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg(lean_object* v_msgData_271_, lean_object* v_macroStack_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_options_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_options_275_ = lean_ctor_get(v___y_273_, 2);
v___x_276_ = l_Lean_Elab_pp_macroStack;
v___x_277_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__6(v_options_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
lean_dec(v_macroStack_272_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v_msgData_271_);
return v___x_278_;
}
else
{
if (lean_obj_tag(v_macroStack_272_) == 0)
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v_msgData_271_);
return v___x_279_;
}
else
{
lean_object* v_head_280_; lean_object* v_after_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_296_; 
v_head_280_ = lean_ctor_get(v_macroStack_272_, 0);
lean_inc(v_head_280_);
v_after_281_ = lean_ctor_get(v_head_280_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_head_280_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v_head_280_, 0);
lean_dec(v_unused_297_);
v___x_283_ = v_head_280_;
v_isShared_284_ = v_isSharedCheck_296_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_after_281_);
lean_dec(v_head_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_296_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7___closed__0);
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 7);
lean_ctor_set(v___x_283_, 1, v___x_285_);
lean_ctor_set(v___x_283_, 0, v_msgData_271_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_msgData_271_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_285_);
v___x_287_ = v_reuseFailAlloc_295_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_msgData_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_288_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___closed__2);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = l_Lean_MessageData_ofSyntax(v_after_281_);
v___x_291_ = l_Lean_indentD(v___x_290_);
v_msgData_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_292_, 0, v___x_289_);
lean_ctor_set(v_msgData_292_, 1, v___x_291_);
v___x_293_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4_spec__7(v_msgData_292_, v_macroStack_272_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_298_, lean_object* v_macroStack_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg(v_msgData_298_, v_macroStack_299_, v___y_300_);
lean_dec_ref(v___y_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_ref_311_; lean_object* v___x_312_; lean_object* v_a_313_; lean_object* v_macroStack_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_325_; 
v_ref_311_ = lean_ctor_get(v___y_308_, 5);
v___x_312_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__3(v_msg_303_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref(v___x_312_);
v_macroStack_314_ = lean_ctor_get(v___y_304_, 1);
v___x_315_ = l_Lean_Elab_getBetterRef(v_ref_311_, v_macroStack_314_);
lean_inc(v_macroStack_314_);
v___x_316_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg(v_a_313_, v_macroStack_314_, v___y_308_);
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_325_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_315_);
lean_ctor_set(v___x_321_, 1, v_a_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 1);
lean_ctor_set(v___x_319_, 0, v___x_321_);
v___x_323_ = v___x_319_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___boxed(lean_object* v_msg_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v_msg_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0(lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_ref_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_ref_342_ = lean_ctor_get(v___y_339_, 5);
v___x_343_ = 0;
v___x_344_ = l_Lean_SourceInfo_fromRef(v_ref_342_, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0___boxed(lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0(v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_353_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__13(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__12));
v___x_379_ = l_String_toRawSubstring_x27(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__33(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__32));
v___x_426_ = l_String_toRawSubstring_x27(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__43(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__42));
v___x_449_ = l_String_toRawSubstring_x27(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__52(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__51));
v___x_471_ = l_String_toRawSubstring_x27(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(lean_object* v___f_488_, lean_object* v___x_489_, lean_object* v___x_490_, lean_object* v___x_491_, lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v_____r_495_, lean_object* v_fields_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___y_505_; lean_object* v___x_628_; 
lean_inc_ref(v___x_494_);
v___x_628_ = l_Lean_Meta_isType(v___x_494_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; uint8_t v___x_630_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
v___x_630_ = lean_unbox(v_a_629_);
lean_dec(v_a_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
lean_dec_ref(v___x_628_);
v___x_631_ = l_Lean_Meta_isProof(v___x_494_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
v___y_505_ = v___x_631_;
goto v___jp_504_;
}
else
{
lean_dec_ref(v___x_494_);
v___y_505_ = v___x_628_;
goto v___jp_504_;
}
}
else
{
lean_dec_ref(v___x_494_);
v___y_505_ = v___x_628_;
goto v___jp_504_;
}
v___jp_504_:
{
if (lean_obj_tag(v___y_505_) == 0)
{
lean_object* v_a_506_; uint8_t v___x_507_; 
v_a_506_ = lean_ctor_get(v___y_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___y_505_);
v___x_507_ = lean_unbox(v_a_506_);
lean_dec(v_a_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
v___x_508_ = lean_apply_7(v___f_488_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_580_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_580_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_580_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_580_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_quotContext_513_; lean_object* v_currMacroScope_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v_quotContext_513_ = lean_ctor_get(v___y_501_, 10);
v_currMacroScope_514_ = lean_ctor_get(v___y_501_, 11);
v___x_515_ = lean_string_length(v___x_489_);
v___x_516_ = lean_unsigned_to_nat(4u);
v___x_517_ = lean_nat_add(v___x_515_, v___x_516_);
v___x_518_ = l_Nat_reprFast(v___x_517_);
v___x_519_ = l_Lean_Syntax_mkNumLit(v___x_518_, v___x_490_);
v___x_520_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__1));
v___x_521_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__2));
lean_inc_n(v_a_509_, 25);
v___x_522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_522_, 0, v_a_509_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
lean_inc_ref_n(v___x_522_, 2);
v___x_523_ = l_Lean_Syntax_node3(v_a_509_, v___x_520_, v_fields_496_, v___x_522_, v___x_491_);
v___x_524_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__4));
v___x_525_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__5));
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v_a_509_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_Syntax_node1(v_a_509_, v___x_524_, v___x_526_);
v___x_528_ = l_Lean_Syntax_node3(v_a_509_, v___x_520_, v___x_523_, v___x_522_, v___x_527_);
v___x_529_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__7));
v___x_530_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__9));
v___x_531_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7));
v___x_532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_532_, 0, v_a_509_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__11));
v___x_534_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__13);
v___x_535_ = lean_box(0);
lean_inc_n(v_currMacroScope_514_, 4);
lean_inc_n(v_quotContext_513_, 4);
v___x_536_ = l_Lean_addMacroScope(v_quotContext_513_, v___x_535_, v_currMacroScope_514_);
v___x_537_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__29));
v___x_538_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_538_, 0, v_a_509_);
lean_ctor_set(v___x_538_, 1, v___x_534_);
lean_ctor_set(v___x_538_, 2, v___x_536_);
lean_ctor_set(v___x_538_, 3, v___x_537_);
v___x_539_ = l_Lean_Syntax_node1(v_a_509_, v___x_533_, v___x_538_);
v___x_540_ = l_Lean_Syntax_node2(v_a_509_, v___x_530_, v___x_532_, v___x_539_);
v___x_541_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31));
v___x_542_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__33, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__33_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__33);
v___x_543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__36));
v___x_544_ = l_Lean_addMacroScope(v_quotContext_513_, v___x_543_, v_currMacroScope_514_);
v___x_545_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__41));
v___x_546_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_546_, 0, v_a_509_);
lean_ctor_set(v___x_546_, 1, v___x_542_);
lean_ctor_set(v___x_546_, 2, v___x_544_);
lean_ctor_set(v___x_546_, 3, v___x_545_);
v___x_547_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_548_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__43, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__43_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__43);
v___x_549_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__45));
v___x_550_ = l_Lean_addMacroScope(v_quotContext_513_, v___x_549_, v_currMacroScope_514_);
v___x_551_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__50));
v___x_552_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_552_, 0, v_a_509_);
lean_ctor_set(v___x_552_, 1, v___x_548_);
lean_ctor_set(v___x_552_, 2, v___x_550_);
lean_ctor_set(v___x_552_, 3, v___x_551_);
v___x_553_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__52, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__52_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__52);
v___x_554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__53));
v___x_555_ = l_Lean_addMacroScope(v_quotContext_513_, v___x_554_, v_currMacroScope_514_);
v___x_556_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__55));
v___x_557_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_557_, 0, v_a_509_);
lean_ctor_set(v___x_557_, 1, v___x_553_);
lean_ctor_set(v___x_557_, 2, v___x_555_);
lean_ctor_set(v___x_557_, 3, v___x_556_);
v___x_558_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__57));
v___x_559_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__58));
v___x_560_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_560_, 0, v_a_509_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = lean_mk_syntax_ident(v___x_492_);
v___x_562_ = l_Lean_Syntax_node3(v_a_509_, v___x_558_, v___x_493_, v___x_560_, v___x_561_);
v___x_563_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23));
v___x_564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_564_, 0, v_a_509_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
lean_inc_ref_n(v___x_564_, 3);
lean_inc_n(v___x_540_, 3);
v___x_565_ = l_Lean_Syntax_node3(v_a_509_, v___x_529_, v___x_540_, v___x_562_, v___x_564_);
v___x_566_ = l_Lean_Syntax_node1(v_a_509_, v___x_547_, v___x_565_);
v___x_567_ = l_Lean_Syntax_node2(v_a_509_, v___x_541_, v___x_557_, v___x_566_);
v___x_568_ = l_Lean_Syntax_node3(v_a_509_, v___x_529_, v___x_540_, v___x_567_, v___x_564_);
v___x_569_ = l_Lean_Syntax_node2(v_a_509_, v___x_547_, v___x_519_, v___x_568_);
v___x_570_ = l_Lean_Syntax_node2(v_a_509_, v___x_541_, v___x_552_, v___x_569_);
v___x_571_ = l_Lean_Syntax_node3(v_a_509_, v___x_529_, v___x_540_, v___x_570_, v___x_564_);
v___x_572_ = l_Lean_Syntax_node1(v_a_509_, v___x_547_, v___x_571_);
v___x_573_ = l_Lean_Syntax_node2(v_a_509_, v___x_541_, v___x_546_, v___x_572_);
v___x_574_ = l_Lean_Syntax_node3(v_a_509_, v___x_529_, v___x_540_, v___x_573_, v___x_564_);
v___x_575_ = l_Lean_Syntax_node3(v_a_509_, v___x_520_, v___x_528_, v___x_522_, v___x_574_);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_576_);
v___x_578_ = v___x_511_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec(v_fields_496_);
lean_dec(v___x_493_);
lean_dec(v___x_492_);
lean_dec(v___x_491_);
lean_dec(v___x_490_);
v_a_581_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_508_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_508_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v___x_589_; 
lean_dec(v___x_493_);
lean_dec(v___x_492_);
lean_dec(v___x_490_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
v___x_589_ = lean_apply_7(v___f_488_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_611_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_611_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_611_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_611_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_594_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__1));
v___x_595_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__2));
lean_inc_n(v_a_590_, 7);
v___x_596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_596_, 0, v_a_590_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
lean_inc_ref_n(v___x_596_, 2);
v___x_597_ = l_Lean_Syntax_node3(v_a_590_, v___x_594_, v_fields_496_, v___x_596_, v___x_491_);
v___x_598_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__4));
v___x_599_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__5));
v___x_600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_600_, 0, v_a_590_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Lean_Syntax_node1(v_a_590_, v___x_598_, v___x_600_);
v___x_602_ = l_Lean_Syntax_node3(v_a_590_, v___x_594_, v___x_597_, v___x_596_, v___x_601_);
v___x_603_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__59));
v___x_604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_604_, 0, v_a_590_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = l_Lean_Syntax_node1(v_a_590_, v___x_598_, v___x_604_);
v___x_606_ = l_Lean_Syntax_node3(v_a_590_, v___x_594_, v___x_602_, v___x_596_, v___x_605_);
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_607_);
v___x_609_ = v___x_592_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_fields_496_);
lean_dec(v___x_491_);
v_a_612_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_589_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_589_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_fields_496_);
lean_dec(v___x_493_);
lean_dec(v___x_492_);
lean_dec(v___x_491_);
lean_dec(v___x_490_);
lean_dec_ref(v___f_488_);
v_a_620_ = lean_ctor_get(v___y_505_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___y_505_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___y_505_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___y_505_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___boxed(lean_object* v___f_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v___x_635_, lean_object* v___x_636_, lean_object* v___x_637_, lean_object* v___x_638_, lean_object* v_____r_639_, lean_object* v_fields_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(v___f_632_, v___x_633_, v___x_634_, v___x_635_, v___x_636_, v___x_637_, v___x_638_, v_____r_639_, v_fields_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v___x_633_);
return v_res_648_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__2));
v___x_653_ = l_String_toRawSubstring_x27(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(lean_object* v_upperBound_673_, lean_object* v___x_674_, lean_object* v___x_675_, lean_object* v_xs_676_, lean_object* v___x_677_, lean_object* v_a_678_, lean_object* v_b_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___y_688_; uint8_t v___x_710_; 
v___x_710_ = lean_nat_dec_lt(v_a_678_, v_upperBound_673_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
lean_dec(v_a_678_);
lean_dec(v___x_677_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v_b_679_);
return v___x_711_;
}
else
{
lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___f_712_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__0));
v___x_713_ = l_Lean_instInhabitedExpr;
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_array_fget_borrowed(v___x_674_, v_a_678_);
lean_inc(v___x_715_);
v___x_716_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_715_, v___x_710_);
v___x_717_ = lean_box(2);
lean_inc_ref(v___x_716_);
v___x_718_ = l_Lean_Syntax_mkStrLit(v___x_716_, v___x_717_);
v___x_719_ = lean_nat_add(v___x_675_, v_a_678_);
v___x_720_ = lean_array_get_borrowed(v___x_713_, v_xs_676_, v___x_719_);
lean_dec(v___x_719_);
v___x_721_ = lean_nat_dec_eq(v_a_678_, v___x_714_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
v___x_722_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0(v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v_quotContext_724_; lean_object* v_currMacroScope_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_n(v_a_723_, 6);
lean_dec_ref(v___x_722_);
v_quotContext_724_ = lean_ctor_get(v___y_684_, 10);
v_currMacroScope_725_ = lean_ctor_get(v___y_684_, 11);
v___x_726_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__1));
v___x_727_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__2));
v___x_728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_728_, 0, v_a_723_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__4));
v___x_730_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__1));
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v_a_723_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_Syntax_node1(v_a_723_, v___x_729_, v___x_731_);
lean_inc_ref(v___x_728_);
v___x_733_ = l_Lean_Syntax_node3(v_a_723_, v___x_726_, v_b_679_, v___x_728_, v___x_732_);
v___x_734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3);
v___x_735_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__5));
lean_inc(v_currMacroScope_725_);
lean_inc(v_quotContext_724_);
v___x_736_ = l_Lean_addMacroScope(v_quotContext_724_, v___x_735_, v_currMacroScope_725_);
v___x_737_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__10));
v___x_738_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_738_, 0, v_a_723_);
lean_ctor_set(v___x_738_, 1, v___x_734_);
lean_ctor_set(v___x_738_, 2, v___x_736_);
lean_ctor_set(v___x_738_, 3, v___x_737_);
v___x_739_ = l_Lean_Syntax_node3(v_a_723_, v___x_726_, v___x_733_, v___x_728_, v___x_738_);
v___x_740_ = lean_box(0);
lean_inc(v___x_720_);
lean_inc(v___x_677_);
lean_inc(v___x_715_);
v___x_741_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(v___f_712_, v___x_716_, v___x_717_, v___x_718_, v___x_715_, v___x_677_, v___x_720_, v___x_740_, v___x_739_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec_ref(v___x_716_);
v___y_688_ = v___x_741_;
goto v___jp_687_;
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v___x_718_);
lean_dec_ref(v___x_716_);
lean_dec(v_b_679_);
lean_dec(v_a_678_);
lean_dec(v___x_677_);
v_a_742_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_722_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_722_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_box(0);
lean_inc(v___x_720_);
lean_inc(v___x_677_);
lean_inc(v___x_715_);
v___x_751_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1(v___f_712_, v___x_716_, v___x_717_, v___x_718_, v___x_715_, v___x_677_, v___x_720_, v___x_750_, v_b_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec_ref(v___x_716_);
v___y_688_ = v___x_751_;
goto v___jp_687_;
}
}
v___jp_687_:
{
if (lean_obj_tag(v___y_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_701_; 
v_a_689_ = lean_ctor_get(v___y_688_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___y_688_);
if (v_isSharedCheck_701_ == 0)
{
v___x_691_ = v___y_688_;
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___y_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
if (lean_obj_tag(v_a_689_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; 
lean_dec(v_a_678_);
lean_dec(v___x_677_);
v_a_693_ = lean_ctor_get(v_a_689_, 0);
lean_inc(v_a_693_);
lean_dec_ref(v_a_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v_a_693_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
lean_del_object(v___x_691_);
v_a_697_ = lean_ctor_get(v_a_689_, 0);
lean_inc(v_a_697_);
lean_dec_ref(v_a_689_);
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = lean_nat_add(v_a_678_, v___x_698_);
lean_dec(v_a_678_);
v_a_678_ = v___x_699_;
v_b_679_ = v_a_697_;
goto _start;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec(v_a_678_);
lean_dec(v___x_677_);
v_a_702_ = lean_ctor_get(v___y_688_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___y_688_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___y_688_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___y_688_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___boxed(lean_object* v_upperBound_752_, lean_object* v___x_753_, lean_object* v___x_754_, lean_object* v_xs_755_, lean_object* v___x_756_, lean_object* v_a_757_, lean_object* v_b_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v_upperBound_752_, v___x_753_, v___x_754_, v_xs_755_, v___x_756_, v_a_757_, v_b_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec_ref(v_xs_755_);
lean_dec(v___x_754_);
lean_dec_ref(v___x_753_);
lean_dec(v_upperBound_752_);
return v_res_766_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0));
v___x_769_ = l_String_toRawSubstring_x27(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9));
v___x_791_ = l_String_toRawSubstring_x27(v___x_790_);
return v___x_791_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18));
v___x_810_ = l_Lean_stringToMessageData(v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(lean_object* v___x_811_, lean_object* v_numParams_812_, lean_object* v___x_813_, lean_object* v___x_814_, lean_object* v_xs_815_, lean_object* v_x_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_ref_824_; lean_object* v_quotContext_825_; lean_object* v_currMacroScope_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_ref_824_ = lean_ctor_get(v___y_821_, 5);
v_quotContext_825_ = lean_ctor_get(v___y_821_, 10);
v_currMacroScope_826_ = lean_ctor_get(v___y_821_, 11);
v___x_827_ = 0;
v___x_828_ = l_Lean_SourceInfo_fromRef(v_ref_824_, v___x_827_);
v___x_829_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1);
v___x_830_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3));
lean_inc(v_currMacroScope_826_);
lean_inc(v_quotContext_825_);
v___x_831_ = l_Lean_addMacroScope(v_quotContext_825_, v___x_830_, v_currMacroScope_826_);
v___x_832_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8));
v___x_833_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_833_, 0, v___x_828_);
lean_ctor_set(v___x_833_, 1, v___x_829_);
lean_ctor_set(v___x_833_, 2, v___x_831_);
lean_ctor_set(v___x_833_, 3, v___x_832_);
v___x_871_ = lean_array_get_size(v_xs_815_);
v___x_872_ = lean_array_get_size(v___x_811_);
v___x_873_ = lean_nat_add(v_numParams_812_, v___x_872_);
v___x_874_ = lean_nat_dec_eq(v___x_871_, v___x_873_);
lean_dec(v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v___x_833_);
lean_dec(v___x_814_);
lean_dec(v___x_813_);
v___x_875_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19);
v___x_876_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v___x_875_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
v___y_835_ = v___y_817_;
v___y_836_ = v___y_818_;
v___y_837_ = v___y_819_;
v___y_838_ = v___y_820_;
v___y_839_ = v___y_821_;
v___y_840_ = v___y_822_;
goto v___jp_834_;
}
v___jp_834_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_array_get_size(v___x_811_);
v___x_842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_841_, v___x_811_, v_numParams_812_, v_xs_815_, v___x_813_, v___x_814_, v___x_833_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_870_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_870_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_870_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_870_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_ref_847_; lean_object* v_quotContext_848_; lean_object* v_currMacroScope_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v_ref_847_ = lean_ctor_get(v___y_839_, 5);
v_quotContext_848_ = lean_ctor_get(v___y_839_, 10);
v_currMacroScope_849_ = lean_ctor_get(v___y_839_, 11);
v___x_850_ = l_Lean_SourceInfo_fromRef(v_ref_847_, v___x_827_);
v___x_851_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31));
v___x_852_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10);
v___x_853_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12));
lean_inc(v_currMacroScope_849_);
lean_inc(v_quotContext_848_);
v___x_854_ = l_Lean_addMacroScope(v_quotContext_848_, v___x_853_, v_currMacroScope_849_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15));
lean_inc_n(v___x_850_, 6);
v___x_856_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_856_, 0, v___x_850_);
lean_ctor_set(v___x_856_, 1, v___x_852_);
lean_ctor_set(v___x_856_, 2, v___x_854_);
lean_ctor_set(v___x_856_, 3, v___x_855_);
v___x_857_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_858_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__4));
v___x_859_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16));
v___x_860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_850_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = l_Lean_Syntax_node1(v___x_850_, v___x_858_, v___x_860_);
v___x_862_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17));
v___x_863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_850_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Lean_Syntax_node1(v___x_850_, v___x_858_, v___x_863_);
v___x_865_ = l_Lean_Syntax_node3(v___x_850_, v___x_857_, v___x_861_, v_a_843_, v___x_864_);
v___x_866_ = l_Lean_Syntax_node2(v___x_850_, v___x_851_, v___x_856_, v___x_865_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_866_);
v___x_868_ = v___x_845_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed(lean_object* v___x_885_, lean_object* v_numParams_886_, lean_object* v___x_887_, lean_object* v___x_888_, lean_object* v_xs_889_, lean_object* v_x_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(v___x_885_, v_numParams_886_, v___x_887_, v___x_888_, v_xs_889_, v_x_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec_ref(v_x_890_);
lean_dec_ref(v_xs_889_);
lean_dec(v_numParams_886_);
lean_dec_ref(v___x_885_);
return v_res_898_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_instMonadEIO(lean_box(0));
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(lean_object* v_msg_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v_toApplicative_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_1007_; 
v___x_914_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0);
v___x_915_ = l_StateRefT_x27_instMonad___redArg(v___x_914_);
v_toApplicative_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; 
v_unused_1008_ = lean_ctor_get(v___x_915_, 1);
lean_dec(v_unused_1008_);
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_1007_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_toApplicative_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_1007_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_toFunctor_920_; lean_object* v_toSeq_921_; lean_object* v_toSeqLeft_922_; lean_object* v_toSeqRight_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_1005_; 
v_toFunctor_920_ = lean_ctor_get(v_toApplicative_916_, 0);
v_toSeq_921_ = lean_ctor_get(v_toApplicative_916_, 2);
v_toSeqLeft_922_ = lean_ctor_get(v_toApplicative_916_, 3);
v_toSeqRight_923_ = lean_ctor_get(v_toApplicative_916_, 4);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_toApplicative_916_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; 
v_unused_1006_ = lean_ctor_get(v_toApplicative_916_, 1);
lean_dec(v_unused_1006_);
v___x_925_ = v_toApplicative_916_;
v_isShared_926_ = v_isSharedCheck_1005_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_toSeqRight_923_);
lean_inc(v_toSeqLeft_922_);
lean_inc(v_toSeq_921_);
lean_inc(v_toFunctor_920_);
lean_dec(v_toApplicative_916_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_1005_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___f_927_; lean_object* v___f_928_; lean_object* v___f_929_; lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___f_932_; lean_object* v___f_933_; lean_object* v___f_934_; lean_object* v___x_936_; 
v___f_927_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1));
v___f_928_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_920_);
v___f_929_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_929_, 0, v_toFunctor_920_);
v___f_930_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_930_, 0, v_toFunctor_920_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___f_929_);
lean_ctor_set(v___x_931_, 1, v___f_930_);
v___f_932_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_932_, 0, v_toSeqRight_923_);
v___f_933_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_933_, 0, v_toSeqLeft_922_);
v___f_934_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_934_, 0, v_toSeq_921_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 4, v___f_932_);
lean_ctor_set(v___x_925_, 3, v___f_933_);
lean_ctor_set(v___x_925_, 2, v___f_934_);
lean_ctor_set(v___x_925_, 1, v___f_927_);
lean_ctor_set(v___x_925_, 0, v___x_931_);
v___x_936_ = v___x_925_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___f_927_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v___f_934_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v___f_933_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v___f_932_);
v___x_936_ = v_reuseFailAlloc_1004_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_938_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v___f_928_);
lean_ctor_set(v___x_918_, 0, v___x_936_);
v___x_938_ = v___x_918_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___f_928_);
v___x_938_ = v_reuseFailAlloc_1003_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v_toApplicative_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_1001_; 
v___x_939_ = l_StateRefT_x27_instMonad___redArg(v___x_938_);
v_toApplicative_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_1001_ == 0)
{
lean_object* v_unused_1002_; 
v_unused_1002_ = lean_ctor_get(v___x_939_, 1);
lean_dec(v_unused_1002_);
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_1001_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_toApplicative_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_1001_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_toFunctor_944_; lean_object* v_toSeq_945_; lean_object* v_toSeqLeft_946_; lean_object* v_toSeqRight_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_999_; 
v_toFunctor_944_ = lean_ctor_get(v_toApplicative_940_, 0);
v_toSeq_945_ = lean_ctor_get(v_toApplicative_940_, 2);
v_toSeqLeft_946_ = lean_ctor_get(v_toApplicative_940_, 3);
v_toSeqRight_947_ = lean_ctor_get(v_toApplicative_940_, 4);
v_isSharedCheck_999_ = !lean_is_exclusive(v_toApplicative_940_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v_toApplicative_940_, 1);
lean_dec(v_unused_1000_);
v___x_949_ = v_toApplicative_940_;
v_isShared_950_ = v_isSharedCheck_999_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_toSeqRight_947_);
lean_inc(v_toSeqLeft_946_);
lean_inc(v_toSeq_945_);
lean_inc(v_toFunctor_944_);
lean_dec(v_toApplicative_940_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_999_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___f_951_; lean_object* v___f_952_; lean_object* v___f_953_; lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___f_956_; lean_object* v___f_957_; lean_object* v___f_958_; lean_object* v___x_960_; 
v___f_951_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3));
v___f_952_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_944_);
v___f_953_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_953_, 0, v_toFunctor_944_);
v___f_954_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_954_, 0, v_toFunctor_944_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v___f_953_);
lean_ctor_set(v___x_955_, 1, v___f_954_);
v___f_956_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_956_, 0, v_toSeqRight_947_);
v___f_957_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_957_, 0, v_toSeqLeft_946_);
v___f_958_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_958_, 0, v_toSeq_945_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 4, v___f_956_);
lean_ctor_set(v___x_949_, 3, v___f_957_);
lean_ctor_set(v___x_949_, 2, v___f_958_);
lean_ctor_set(v___x_949_, 1, v___f_951_);
lean_ctor_set(v___x_949_, 0, v___x_955_);
v___x_960_ = v___x_949_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v___f_951_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v___f_958_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v___f_957_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v___f_956_);
v___x_960_ = v_reuseFailAlloc_998_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___f_952_);
lean_ctor_set(v___x_942_, 0, v___x_960_);
v___x_962_ = v___x_942_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___f_952_);
v___x_962_ = v_reuseFailAlloc_997_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v_toApplicative_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_995_; 
v___x_963_ = l_StateRefT_x27_instMonad___redArg(v___x_962_);
v_toApplicative_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v___x_963_, 1);
lean_dec(v_unused_996_);
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_995_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_toApplicative_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_995_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_toFunctor_968_; lean_object* v_toSeq_969_; lean_object* v_toSeqLeft_970_; lean_object* v_toSeqRight_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_993_; 
v_toFunctor_968_ = lean_ctor_get(v_toApplicative_964_, 0);
v_toSeq_969_ = lean_ctor_get(v_toApplicative_964_, 2);
v_toSeqLeft_970_ = lean_ctor_get(v_toApplicative_964_, 3);
v_toSeqRight_971_ = lean_ctor_get(v_toApplicative_964_, 4);
v_isSharedCheck_993_ = !lean_is_exclusive(v_toApplicative_964_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v_toApplicative_964_, 1);
lean_dec(v_unused_994_);
v___x_973_ = v_toApplicative_964_;
v_isShared_974_ = v_isSharedCheck_993_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_toSeqRight_971_);
lean_inc(v_toSeqLeft_970_);
lean_inc(v_toSeq_969_);
lean_inc(v_toFunctor_968_);
lean_dec(v_toApplicative_964_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_993_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___f_977_; lean_object* v___f_978_; lean_object* v___x_979_; lean_object* v___f_980_; lean_object* v___f_981_; lean_object* v___f_982_; lean_object* v___x_984_; 
v___f_975_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5));
v___f_976_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6));
lean_inc_ref(v_toFunctor_968_);
v___f_977_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_977_, 0, v_toFunctor_968_);
v___f_978_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_978_, 0, v_toFunctor_968_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v___f_977_);
lean_ctor_set(v___x_979_, 1, v___f_978_);
v___f_980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_980_, 0, v_toSeqRight_971_);
v___f_981_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_981_, 0, v_toSeqLeft_970_);
v___f_982_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_982_, 0, v_toSeq_969_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 4, v___f_980_);
lean_ctor_set(v___x_973_, 3, v___f_981_);
lean_ctor_set(v___x_973_, 2, v___f_982_);
lean_ctor_set(v___x_973_, 1, v___f_975_);
lean_ctor_set(v___x_973_, 0, v___x_979_);
v___x_984_ = v___x_973_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___f_975_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v___f_982_);
lean_ctor_set(v_reuseFailAlloc_992_, 3, v___f_981_);
lean_ctor_set(v_reuseFailAlloc_992_, 4, v___f_980_);
v___x_984_ = v_reuseFailAlloc_992_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v___f_976_);
lean_ctor_set(v___x_966_, 0, v___x_984_);
v___x_986_ = v___x_966_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___f_976_);
v___x_986_ = v_reuseFailAlloc_991_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_16481__overap_989_; lean_object* v___x_990_; 
v___x_987_ = lean_box(0);
v___x_988_ = l_instInhabitedOfMonad___redArg(v___x_986_, v___x_987_);
v___x_16481__overap_989_ = lean_panic_fn_borrowed(v___x_988_, v_msg_906_);
lean_dec(v___x_988_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
v___x_990_ = lean_apply_7(v___x_16481__overap_989_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, lean_box(0));
return v___x_990_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___boxed(lean_object* v_msg_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(v_msg_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1017_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1027_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6));
v___x_1028_ = lean_unsigned_to_nat(11u);
v___x_1029_ = lean_unsigned_to_nat(122u);
v___x_1030_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5));
v___x_1031_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4));
v___x_1032_ = l_mkPanicMessageWithDecl(v___x_1031_, v___x_1030_, v___x_1029_, v___x_1028_, v___x_1027_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(lean_object* v_constName_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1049_; lean_object* v_env_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = lean_st_ref_get(v___y_1039_);
v_env_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc_ref(v_env_1050_);
lean_dec(v___x_1049_);
v___x_1051_ = 0;
lean_inc(v_constName_1033_);
v___x_1052_ = l_Lean_Environment_findAsync_x3f(v_env_1050_, v_constName_1033_, v___x_1051_);
if (lean_obj_tag(v___x_1052_) == 1)
{
lean_object* v_val_1053_; uint8_t v_kind_1054_; 
v_val_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_val_1053_);
lean_dec_ref(v___x_1052_);
v_kind_1054_ = lean_ctor_get_uint8(v_val_1053_, sizeof(void*)*3);
if (v_kind_1054_ == 6)
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1053_);
if (lean_obj_tag(v___x_1055_) == 6)
{
lean_object* v_val_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_constName_1033_);
v_val_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_val_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 0);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_val_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec_ref(v___x_1055_);
v___x_1064_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7);
v___x_1065_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(v___x_1064_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1074_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1068_ = v___x_1065_;
v_isShared_1069_ = v_isSharedCheck_1074_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1074_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
if (lean_obj_tag(v_a_1066_) == 0)
{
lean_del_object(v___x_1068_);
goto v___jp_1041_;
}
else
{
lean_object* v_val_1070_; lean_object* v___x_1072_; 
lean_dec(v_constName_1033_);
v_val_1070_ = lean_ctor_get(v_a_1066_, 0);
lean_inc(v_val_1070_);
lean_dec_ref(v_a_1066_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v_val_1070_);
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_val_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_constName_1033_);
v_a_1075_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1065_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1065_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
else
{
lean_dec(v_val_1053_);
goto v___jp_1041_;
}
}
else
{
lean_dec(v___x_1052_);
goto v___jp_1041_;
}
v___jp_1041_:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1042_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1);
v___x_1043_ = 0;
v___x_1044_ = l_Lean_MessageData_ofConstName(v_constName_1033_, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1042_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v___x_1047_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___boxed(lean_object* v_constName_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v_constName_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct(lean_object* v_header_1092_, lean_object* v_indVal_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v_toConstantVal_1101_; lean_object* v_numParams_1102_; lean_object* v_ctors_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_toConstantVal_1101_ = lean_ctor_get(v_indVal_1093_, 0);
lean_inc_ref(v_toConstantVal_1101_);
v_numParams_1102_ = lean_ctor_get(v_indVal_1093_, 1);
lean_inc(v_numParams_1102_);
v_ctors_1103_ = lean_ctor_get(v_indVal_1093_, 4);
lean_inc(v_ctors_1103_);
lean_dec_ref(v_indVal_1093_);
v___x_1104_ = lean_box(0);
v___x_1105_ = l_List_head_x21___redArg(v___x_1104_, v_ctors_1103_);
lean_dec(v_ctors_1103_);
v___x_1106_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v___x_1105_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1108_; lean_object* v_toConstantVal_1109_; lean_object* v_env_1110_; lean_object* v_name_1111_; lean_object* v_targetNames_1112_; lean_object* v_type_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___f_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref(v___x_1106_);
v___x_1108_ = lean_st_ref_get(v_a_1099_);
v_toConstantVal_1109_ = lean_ctor_get(v_a_1107_, 0);
lean_inc_ref(v_toConstantVal_1109_);
lean_dec(v_a_1107_);
v_env_1110_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_env_1110_);
lean_dec(v___x_1108_);
v_name_1111_ = lean_ctor_get(v_toConstantVal_1101_, 0);
lean_inc(v_name_1111_);
lean_dec_ref(v_toConstantVal_1101_);
v_targetNames_1112_ = lean_ctor_get(v_header_1092_, 2);
v_type_1113_ = lean_ctor_get(v_toConstantVal_1109_, 2);
lean_inc_ref(v_type_1113_);
lean_dec_ref(v_toConstantVal_1109_);
v___x_1114_ = l_Lean_getStructureFields(v_env_1110_, v_name_1111_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_array_get_borrowed(v___x_1104_, v_targetNames_1112_, v___x_1115_);
lean_inc(v___x_1116_);
v___x_1117_ = lean_mk_syntax_ident(v___x_1116_);
v___f_1118_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1118_, 0, v___x_1114_);
lean_closure_set(v___f_1118_, 1, v_numParams_1102_);
lean_closure_set(v___f_1118_, 2, v___x_1117_);
lean_closure_set(v___f_1118_, 3, v___x_1115_);
v___x_1119_ = 0;
v___x_1120_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v_type_1113_, v___f_1118_, v___x_1119_, v___x_1119_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
return v___x_1120_;
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_numParams_1102_);
lean_dec_ref(v_toConstantVal_1101_);
v_a_1121_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1106_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1106_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___boxed(lean_object* v_header_1129_, lean_object* v_indVal_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(v_header_1129_, v_indVal_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec_ref(v_header_1129_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(lean_object* v_upperBound_1139_, lean_object* v___x_1140_, lean_object* v___x_1141_, lean_object* v_xs_1142_, lean_object* v___x_1143_, lean_object* v_inst_1144_, lean_object* v_R_1145_, lean_object* v_a_1146_, lean_object* v_b_1147_, lean_object* v_c_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v_upperBound_1139_, v___x_1140_, v___x_1141_, v_xs_1142_, v___x_1143_, v_a_1146_, v_b_1147_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1157_ = _args[0];
lean_object* v___x_1158_ = _args[1];
lean_object* v___x_1159_ = _args[2];
lean_object* v_xs_1160_ = _args[3];
lean_object* v___x_1161_ = _args[4];
lean_object* v_inst_1162_ = _args[5];
lean_object* v_R_1163_ = _args[6];
lean_object* v_a_1164_ = _args[7];
lean_object* v_b_1165_ = _args[8];
lean_object* v_c_1166_ = _args[9];
lean_object* v___y_1167_ = _args[10];
lean_object* v___y_1168_ = _args[11];
lean_object* v___y_1169_ = _args[12];
lean_object* v___y_1170_ = _args[13];
lean_object* v___y_1171_ = _args[14];
lean_object* v___y_1172_ = _args[15];
lean_object* v___y_1173_ = _args[16];
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(v_upperBound_1157_, v___x_1158_, v___x_1159_, v_xs_1160_, v___x_1161_, v_inst_1162_, v_R_1163_, v_a_1164_, v_b_1165_, v_c_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v_xs_1160_);
lean_dec(v___x_1159_);
lean_dec_ref(v___x_1158_);
lean_dec(v_upperBound_1157_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(lean_object* v_00_u03b1_1175_, lean_object* v_msg_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v_msg_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___boxed(lean_object* v_00_u03b1_1185_, lean_object* v_msg_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(v_00_u03b1_1185_, v_msg_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4(lean_object* v_msgData_1195_, lean_object* v_macroStack_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___redArg(v_msgData_1195_, v_macroStack_1196_, v___y_1201_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4___boxed(lean_object* v_msgData_1205_, lean_object* v_macroStack_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__4(v_msgData_1205_, v_macroStack_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(lean_object* v_upperBound_1222_, lean_object* v_a_1223_, lean_object* v_b_1224_, lean_object* v___y_1225_){
_start:
{
uint8_t v___x_1227_; 
v___x_1227_ = lean_nat_dec_lt(v_a_1223_, v_upperBound_1222_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; 
lean_dec(v_a_1223_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v_b_1224_);
return v___x_1228_;
}
else
{
lean_object* v_ref_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_ref_1229_ = lean_ctor_get(v___y_1225_, 5);
v___x_1230_ = 0;
v___x_1231_ = l_Lean_SourceInfo_fromRef(v_ref_1229_, v___x_1230_);
v___x_1232_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1));
v___x_1233_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2));
lean_inc(v___x_1231_);
v___x_1234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1231_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Lean_Syntax_node1(v___x_1231_, v___x_1232_, v___x_1234_);
v___x_1236_ = lean_array_push(v_b_1224_, v___x_1235_);
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_nat_add(v_a_1223_, v___x_1237_);
lean_dec(v_a_1223_);
v_a_1223_ = v___x_1238_;
v_b_1224_ = v___x_1236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object* v_upperBound_1240_, lean_object* v_a_1241_, lean_object* v_b_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_1240_, v_a_1241_, v_b_1242_, v___y_1243_);
lean_dec_ref(v___y_1243_);
lean_dec(v_upperBound_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(size_t v_sz_1246_, size_t v_i_1247_, lean_object* v_bs_1248_){
_start:
{
uint8_t v___x_1249_; 
v___x_1249_ = lean_usize_dec_lt(v_i_1247_, v_sz_1246_);
if (v___x_1249_ == 0)
{
return v_bs_1248_;
}
else
{
lean_object* v_v_1250_; lean_object* v___x_1251_; lean_object* v_bs_x27_1252_; size_t v___x_1253_; size_t v___x_1254_; lean_object* v___x_1255_; 
v_v_1250_ = lean_array_uget(v_bs_1248_, v_i_1247_);
v___x_1251_ = lean_unsigned_to_nat(0u);
v_bs_x27_1252_ = lean_array_uset(v_bs_1248_, v_i_1247_, v___x_1251_);
v___x_1253_ = ((size_t)1ULL);
v___x_1254_ = lean_usize_add(v_i_1247_, v___x_1253_);
v___x_1255_ = lean_array_uset(v_bs_x27_1252_, v_i_1247_, v_v_1250_);
v_i_1247_ = v___x_1254_;
v_bs_1248_ = v___x_1255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___boxed(lean_object* v_sz_1257_, lean_object* v_i_1258_, lean_object* v_bs_1259_){
_start:
{
size_t v_sz_boxed_1260_; size_t v_i_boxed_1261_; lean_object* v_res_1262_; 
v_sz_boxed_1260_ = lean_unbox_usize(v_sz_1257_);
lean_dec(v_sz_1257_);
v_i_boxed_1261_ = lean_unbox_usize(v_i_1258_);
lean_dec(v_i_1258_);
v_res_1262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_boxed_1260_, v_i_boxed_1261_, v_bs_1259_);
return v_res_1262_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0));
v___x_1265_ = l_String_toRawSubstring_x27(v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(lean_object* v___x_1278_, lean_object* v_snd_1279_, lean_object* v_toConstantVal_1280_, lean_object* v___f_1281_, lean_object* v___x_1282_, lean_object* v_auxFunName_1283_, lean_object* v_____r_1284_, lean_object* v_ctorArgs_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___y_1294_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = l_Lean_Expr_fvarId_x21(v___x_1278_);
v___x_1381_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_1380_, v___y_1288_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1449_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1449_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1449_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
uint8_t v___x_1386_; uint8_t v___x_1387_; 
v___x_1386_ = lean_unbox(v_a_1382_);
lean_dec(v_a_1382_);
v___x_1387_ = l_Lean_BinderInfo_isExplicit(v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_dec(v_auxFunName_1283_);
lean_dec(v___x_1282_);
lean_dec_ref(v___f_1281_);
lean_dec_ref(v___x_1278_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_ctorArgs_1285_);
lean_ctor_set(v___x_1388_, 1, v_snd_1279_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1389_);
v___x_1391_ = v___x_1384_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
else
{
lean_object* v___x_1393_; 
lean_del_object(v___x_1384_);
lean_inc(v___y_1291_);
lean_inc_ref(v___y_1290_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
lean_inc_ref(v___x_1278_);
v___x_1393_ = lean_infer_type(v___x_1278_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v_name_1395_; uint8_t v___x_1396_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___x_1393_);
v_name_1395_ = lean_ctor_get(v_toConstantVal_1280_, 0);
v___x_1396_ = l_Lean_Expr_isAppOf(v_a_1394_, v_name_1395_);
lean_dec(v_a_1394_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec(v_auxFunName_1283_);
lean_inc_ref(v___x_1278_);
v___x_1397_ = l_Lean_Meta_isType(v___x_1278_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; uint8_t v___x_1399_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
v___x_1399_ = lean_unbox(v_a_1398_);
lean_dec(v_a_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
lean_dec_ref(v___x_1397_);
v___x_1400_ = l_Lean_Meta_isProof(v___x_1278_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
v___y_1294_ = v___x_1400_;
goto v___jp_1293_;
}
else
{
lean_dec_ref(v___x_1278_);
v___y_1294_ = v___x_1397_;
goto v___jp_1293_;
}
}
else
{
lean_dec_ref(v___x_1278_);
v___y_1294_ = v___x_1397_;
goto v___jp_1293_;
}
}
else
{
lean_object* v___x_1401_; 
lean_dec_ref(v___x_1278_);
lean_inc(v___y_1291_);
lean_inc_ref(v___y_1290_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1401_ = lean_apply_7(v___f_1281_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, lean_box(0));
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1432_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1432_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1432_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_quotContext_1406_; lean_object* v_currMacroScope_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v_quotContext_1406_ = lean_ctor_get(v___y_1290_, 10);
v_currMacroScope_1407_ = lean_ctor_get(v___y_1290_, 11);
v___x_1408_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__1));
v___x_1409_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__2));
lean_inc_n(v_a_1402_, 7);
v___x_1410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1410_, 0, v_a_1402_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3);
v___x_1412_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__5));
lean_inc(v_currMacroScope_1407_);
lean_inc(v_quotContext_1406_);
v___x_1413_ = l_Lean_addMacroScope(v_quotContext_1406_, v___x_1412_, v_currMacroScope_1407_);
v___x_1414_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__10));
v___x_1415_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1415_, 0, v_a_1402_);
lean_ctor_set(v___x_1415_, 1, v___x_1411_);
lean_ctor_set(v___x_1415_, 2, v___x_1413_);
lean_ctor_set(v___x_1415_, 3, v___x_1414_);
lean_inc_ref(v___x_1410_);
v___x_1416_ = l_Lean_Syntax_node3(v_a_1402_, v___x_1408_, v_snd_1279_, v___x_1410_, v___x_1415_);
v___x_1417_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31));
v___x_1418_ = lean_mk_syntax_ident(v_auxFunName_1283_);
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1420_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6));
v___x_1421_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7));
v___x_1422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_a_1402_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = l_Lean_Syntax_node1(v_a_1402_, v___x_1420_, v___x_1422_);
v___x_1424_ = l_Lean_Syntax_node2(v_a_1402_, v___x_1419_, v___x_1282_, v___x_1423_);
v___x_1425_ = l_Lean_Syntax_node2(v_a_1402_, v___x_1417_, v___x_1418_, v___x_1424_);
v___x_1426_ = l_Lean_Syntax_node3(v_a_1402_, v___x_1408_, v___x_1416_, v___x_1410_, v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_ctorArgs_1285_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1428_);
v___x_1430_ = v___x_1404_;
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
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_ctorArgs_1285_);
lean_dec(v_auxFunName_1283_);
lean_dec(v___x_1282_);
lean_dec(v_snd_1279_);
v_a_1433_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1401_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1401_);
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
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref(v_ctorArgs_1285_);
lean_dec(v_auxFunName_1283_);
lean_dec(v___x_1282_);
lean_dec_ref(v___f_1281_);
lean_dec(v_snd_1279_);
lean_dec_ref(v___x_1278_);
v_a_1441_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1393_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1393_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v_ctorArgs_1285_);
lean_dec(v_auxFunName_1283_);
lean_dec(v___x_1282_);
lean_dec_ref(v___f_1281_);
lean_dec(v_snd_1279_);
lean_dec_ref(v___x_1278_);
v_a_1450_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1381_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1381_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
v___jp_1293_:
{
if (lean_obj_tag(v___y_1294_) == 0)
{
lean_object* v_a_1295_; uint8_t v___x_1296_; 
v_a_1295_ = lean_ctor_get(v___y_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref(v___y_1294_);
v___x_1296_ = lean_unbox(v_a_1295_);
lean_dec(v_a_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
lean_inc(v___y_1291_);
lean_inc_ref(v___y_1290_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1297_ = lean_apply_7(v___f_1281_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, lean_box(0));
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1328_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1328_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1328_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_quotContext_1302_; lean_object* v_currMacroScope_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v_quotContext_1302_ = lean_ctor_get(v___y_1290_, 10);
v_currMacroScope_1303_ = lean_ctor_get(v___y_1290_, 11);
v___x_1304_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__1));
v___x_1305_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__2));
lean_inc_n(v_a_1298_, 6);
v___x_1306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_a_1298_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3);
v___x_1308_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__5));
lean_inc_n(v_currMacroScope_1303_, 2);
lean_inc_n(v_quotContext_1302_, 2);
v___x_1309_ = l_Lean_addMacroScope(v_quotContext_1302_, v___x_1308_, v_currMacroScope_1303_);
v___x_1310_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__10));
v___x_1311_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1311_, 0, v_a_1298_);
lean_ctor_set(v___x_1311_, 1, v___x_1307_);
lean_ctor_set(v___x_1311_, 2, v___x_1309_);
lean_ctor_set(v___x_1311_, 3, v___x_1310_);
lean_inc_ref(v___x_1306_);
v___x_1312_ = l_Lean_Syntax_node3(v_a_1298_, v___x_1304_, v_snd_1279_, v___x_1306_, v___x_1311_);
v___x_1313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31));
v___x_1314_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1);
v___x_1315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2));
v___x_1316_ = l_Lean_addMacroScope(v_quotContext_1302_, v___x_1315_, v_currMacroScope_1303_);
v___x_1317_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4));
v___x_1318_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1318_, 0, v_a_1298_);
lean_ctor_set(v___x_1318_, 1, v___x_1314_);
lean_ctor_set(v___x_1318_, 2, v___x_1316_);
lean_ctor_set(v___x_1318_, 3, v___x_1317_);
v___x_1319_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1320_ = l_Lean_Syntax_node1(v_a_1298_, v___x_1319_, v___x_1282_);
v___x_1321_ = l_Lean_Syntax_node2(v_a_1298_, v___x_1313_, v___x_1318_, v___x_1320_);
v___x_1322_ = l_Lean_Syntax_node3(v_a_1298_, v___x_1304_, v___x_1312_, v___x_1306_, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_ctorArgs_1285_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1324_);
v___x_1326_ = v___x_1300_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_ctorArgs_1285_);
lean_dec(v___x_1282_);
lean_dec(v_snd_1279_);
v_a_1329_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1297_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1297_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_object* v___x_1337_; 
lean_dec(v___x_1282_);
lean_inc(v___y_1291_);
lean_inc_ref(v___y_1290_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1337_ = lean_apply_7(v___f_1281_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, lean_box(0));
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1363_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1363_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1363_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_quotContext_1342_; lean_object* v_currMacroScope_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v_quotContext_1342_ = lean_ctor_get(v___y_1290_, 10);
v_currMacroScope_1343_ = lean_ctor_get(v___y_1290_, 11);
v___x_1344_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__1));
v___x_1345_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__2));
lean_inc_n(v_a_1338_, 5);
v___x_1346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_a_1338_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__3);
v___x_1348_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__5));
lean_inc(v_currMacroScope_1343_);
lean_inc(v_quotContext_1342_);
v___x_1349_ = l_Lean_addMacroScope(v_quotContext_1342_, v___x_1348_, v_currMacroScope_1343_);
v___x_1350_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__10));
v___x_1351_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1351_, 0, v_a_1338_);
lean_ctor_set(v___x_1351_, 1, v___x_1347_);
lean_ctor_set(v___x_1351_, 2, v___x_1349_);
lean_ctor_set(v___x_1351_, 3, v___x_1350_);
lean_inc_ref(v___x_1346_);
v___x_1352_ = l_Lean_Syntax_node3(v_a_1338_, v___x_1344_, v_snd_1279_, v___x_1346_, v___x_1351_);
v___x_1353_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__4));
v___x_1354_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__59));
v___x_1355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_a_1338_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_Syntax_node1(v_a_1338_, v___x_1353_, v___x_1355_);
v___x_1357_ = l_Lean_Syntax_node3(v_a_1338_, v___x_1344_, v___x_1352_, v___x_1346_, v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v_ctorArgs_1285_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1359_);
v___x_1361_ = v___x_1340_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v_ctorArgs_1285_);
lean_dec(v_snd_1279_);
v_a_1364_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1337_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1337_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref(v_ctorArgs_1285_);
lean_dec(v___x_1282_);
lean_dec_ref(v___f_1281_);
lean_dec(v_snd_1279_);
v_a_1372_ = lean_ctor_get(v___y_1294_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___y_1294_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___y_1294_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___y_1294_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___boxed(lean_object* v___x_1458_, lean_object* v_snd_1459_, lean_object* v_toConstantVal_1460_, lean_object* v___f_1461_, lean_object* v___x_1462_, lean_object* v_auxFunName_1463_, lean_object* v_____r_1464_, lean_object* v_ctorArgs_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___x_1458_, v_snd_1459_, v_toConstantVal_1460_, v___f_1461_, v___x_1462_, v_auxFunName_1463_, v_____r_1464_, v_ctorArgs_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec_ref(v_toConstantVal_1460_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(lean_object* v_upperBound_1477_, lean_object* v_xs_1478_, lean_object* v_indVal_1479_, lean_object* v_auxFunName_1480_, lean_object* v_header_1481_, lean_object* v_a_1482_, lean_object* v_b_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___y_1492_; uint8_t v___x_1514_; 
v___x_1514_ = lean_nat_dec_lt(v_a_1482_, v_upperBound_1477_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
lean_dec(v_a_1482_);
lean_dec(v_auxFunName_1480_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v_b_1483_);
return v___x_1515_;
}
else
{
lean_object* v_fst_1516_; lean_object* v_snd_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1565_; 
v_fst_1516_ = lean_ctor_get(v_b_1483_, 0);
v_snd_1517_ = lean_ctor_get(v_b_1483_, 1);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_b_1483_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1519_ = v_b_1483_;
v_isShared_1520_ = v_isSharedCheck_1565_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_snd_1517_);
lean_inc(v_fst_1516_);
lean_dec(v_b_1483_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1565_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v_toConstantVal_1521_; lean_object* v_numParams_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v_a_1527_; 
v_toConstantVal_1521_ = lean_ctor_get(v_indVal_1479_, 0);
v_numParams_1522_ = lean_ctor_get(v_indVal_1479_, 1);
v___f_1523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___closed__0));
v___x_1524_ = lean_array_fget_borrowed(v_xs_1478_, v_a_1482_);
v___x_1525_ = lean_nat_dec_lt(v_a_1482_, v_numParams_1522_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1));
v___x_1552_ = l_Lean_Core_mkFreshUserName(v___x_1551_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
v_a_1527_ = v_a_1553_;
goto v___jp_1526_;
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_del_object(v___x_1519_);
lean_dec(v_snd_1517_);
lean_dec(v_fst_1516_);
lean_dec(v_a_1482_);
lean_dec(v_auxFunName_1480_);
v_a_1554_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1552_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1552_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_argNames_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_argNames_1562_ = lean_ctor_get(v_header_1481_, 1);
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_array_get_borrowed(v___x_1563_, v_argNames_1562_, v_a_1482_);
lean_inc(v___x_1564_);
v_a_1527_ = v___x_1564_;
goto v___jp_1526_;
}
v___jp_1526_:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_mk_syntax_ident(v_a_1527_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_del_object(v___x_1519_);
lean_inc(v___x_1528_);
v___x_1529_ = lean_array_push(v_fst_1516_, v___x_1528_);
v___x_1530_ = lean_box(0);
lean_inc(v_auxFunName_1480_);
lean_inc(v___x_1524_);
v___x_1531_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___x_1524_, v_snd_1517_, v_toConstantVal_1521_, v___f_1523_, v___x_1528_, v_auxFunName_1480_, v___x_1530_, v___x_1529_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
v___y_1492_ = v___x_1531_;
goto v___jp_1491_;
}
else
{
lean_object* v___x_1532_; 
v___x_1532_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__0(v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc_n(v_a_1533_, 2);
lean_dec_ref(v___x_1532_);
v___x_1534_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1));
v___x_1535_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2));
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 2);
lean_ctor_set(v___x_1519_, 1, v___x_1535_);
lean_ctor_set(v___x_1519_, 0, v_a_1533_);
v___x_1537_ = v___x_1519_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1533_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1538_ = l_Lean_Syntax_node1(v_a_1533_, v___x_1534_, v___x_1537_);
v___x_1539_ = lean_array_push(v_fst_1516_, v___x_1538_);
v___x_1540_ = lean_box(0);
lean_inc(v_auxFunName_1480_);
lean_inc(v___x_1524_);
v___x_1541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___x_1524_, v_snd_1517_, v_toConstantVal_1521_, v___f_1523_, v___x_1528_, v_auxFunName_1480_, v___x_1540_, v___x_1539_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
v___y_1492_ = v___x_1541_;
goto v___jp_1491_;
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec(v___x_1528_);
lean_del_object(v___x_1519_);
lean_dec(v_snd_1517_);
lean_dec(v_fst_1516_);
lean_dec(v_a_1482_);
lean_dec(v_auxFunName_1480_);
v_a_1543_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1532_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1532_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
}
}
v___jp_1491_:
{
if (lean_obj_tag(v___y_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1505_; 
v_a_1493_ = lean_ctor_get(v___y_1492_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___y_1492_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1495_ = v___y_1492_;
v_isShared_1496_ = v_isSharedCheck_1505_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___y_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1505_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
if (lean_obj_tag(v_a_1493_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; 
lean_dec(v_a_1482_);
lean_dec(v_auxFunName_1480_);
v_a_1497_ = lean_ctor_get(v_a_1493_, 0);
lean_inc(v_a_1497_);
lean_dec_ref(v_a_1493_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v_a_1497_);
v___x_1499_ = v___x_1495_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_del_object(v___x_1495_);
v_a_1501_ = lean_ctor_get(v_a_1493_, 0);
lean_inc(v_a_1501_);
lean_dec_ref(v_a_1493_);
v___x_1502_ = lean_unsigned_to_nat(1u);
v___x_1503_ = lean_nat_add(v_a_1482_, v___x_1502_);
lean_dec(v_a_1482_);
v_a_1482_ = v___x_1503_;
v_b_1483_ = v_a_1501_;
goto _start;
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v_a_1482_);
lean_dec(v_auxFunName_1480_);
v_a_1506_ = lean_ctor_get(v___y_1492_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___y_1492_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___y_1492_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___y_1492_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object* v_upperBound_1566_, lean_object* v_xs_1567_, lean_object* v_indVal_1568_, lean_object* v_auxFunName_1569_, lean_object* v_header_1570_, lean_object* v_a_1571_, lean_object* v_b_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v_upperBound_1566_, v_xs_1567_, v_indVal_1568_, v_auxFunName_1569_, v_header_1570_, v_a_1571_, v_b_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec_ref(v_header_1570_);
lean_dec_ref(v_indVal_1568_);
lean_dec_ref(v_xs_1567_);
lean_dec(v_upperBound_1566_);
return v_res_1580_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4));
v___x_1594_ = l_String_toRawSubstring_x27(v___x_1593_);
return v___x_1594_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15));
v___x_1619_ = l_Lean_mkAtom(v___x_1618_);
return v___x_1619_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18));
v___x_1623_ = l_String_toRawSubstring_x27(v___x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(lean_object* v_indVal_1679_, lean_object* v___x_1680_, lean_object* v_alts_1681_, lean_object* v_name_1682_, lean_object* v_auxFunName_1683_, lean_object* v_header_1684_, lean_object* v___f_1685_, lean_object* v_head_1686_, lean_object* v_xs_1687_, lean_object* v_x_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_numIndices_1696_; lean_object* v___x_1697_; 
v_numIndices_1696_ = lean_ctor_get(v_indVal_1679_, 2);
lean_inc_ref(v_alts_1681_);
lean_inc(v___x_1680_);
v___x_1697_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_numIndices_1696_, v___x_1680_, v_alts_1681_, v___y_1693_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v_ref_1699_; lean_object* v_quotContext_1700_; lean_object* v_currMacroScope_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref(v___x_1697_);
v_ref_1699_ = lean_ctor_get(v___y_1693_, 5);
v_quotContext_1700_ = lean_ctor_get(v___y_1693_, 10);
v_currMacroScope_1701_ = lean_ctor_get(v___y_1693_, 11);
v___x_1702_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1));
v___x_1703_ = lean_box(0);
v___x_1704_ = lean_array_get_size(v_xs_1687_);
v___x_1705_ = 0;
v___x_1706_ = l_Lean_SourceInfo_fromRef(v_ref_1699_, v___x_1705_);
v___x_1707_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5);
lean_inc(v_currMacroScope_1701_);
lean_inc(v_quotContext_1700_);
v___x_1708_ = l_Lean_addMacroScope(v_quotContext_1700_, v___x_1702_, v_currMacroScope_1701_);
v___x_1709_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8));
lean_inc_n(v___x_1706_, 2);
v___x_1710_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1706_);
lean_ctor_set(v___x_1710_, 1, v___x_1707_);
lean_ctor_set(v___x_1710_, 2, v___x_1708_);
lean_ctor_set(v___x_1710_, 3, v___x_1709_);
v___x_1711_ = 1;
v___x_1712_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1682_, v___x_1711_);
v___x_1713_ = lean_box(2);
v___x_1714_ = l_Lean_Syntax_mkStrLit(v___x_1712_, v___x_1713_);
v___x_1715_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1716_ = l_Lean_Syntax_node1(v___x_1706_, v___x_1715_, v___x_1714_);
v___x_1717_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__31));
v___x_1718_ = l_Lean_Syntax_node2(v___x_1706_, v___x_1717_, v___x_1710_, v___x_1716_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v_alts_1681_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v___x_1704_, v_xs_1687_, v_indVal_1679_, v_auxFunName_1683_, v_header_1684_, v___x_1680_, v___x_1719_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1722_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref(v___x_1720_);
lean_inc_ref(v___f_1685_);
lean_inc(v___y_1694_);
lean_inc_ref(v___y_1693_);
lean_inc(v___y_1692_);
lean_inc_ref(v___y_1691_);
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
v___x_1722_ = lean_apply_7(v___f_1685_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, lean_box(0));
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref(v___x_1722_);
lean_inc(v___y_1694_);
lean_inc_ref(v___y_1693_);
lean_inc(v___y_1692_);
lean_inc_ref(v___y_1691_);
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
v___x_1724_ = lean_apply_7(v___f_1685_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, lean_box(0));
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1830_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1830_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1830_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_fst_1729_; lean_object* v_snd_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1829_; 
v_fst_1729_ = lean_ctor_get(v_a_1721_, 0);
v_snd_1730_ = lean_ctor_get(v_a_1721_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_a_1721_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1732_ = v_a_1721_;
v_isShared_1733_ = v_isSharedCheck_1829_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_snd_1730_);
lean_inc(v_fst_1729_);
lean_dec(v_a_1721_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1829_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1734_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9));
lean_inc(v_a_1723_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set_tag(v___x_1732_, 2);
lean_ctor_set(v___x_1732_, 1, v___x_1734_);
lean_ctor_set(v___x_1732_, 0, v_a_1723_);
v___x_1736_ = v___x_1732_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1723_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; size_t v_sz_1748_; size_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1737_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11));
v___x_1738_ = lean_mk_syntax_ident(v_head_1686_);
lean_inc_n(v_a_1723_, 2);
v___x_1739_ = l_Lean_Syntax_node2(v_a_1723_, v___x_1737_, v___x_1736_, v___x_1738_);
v___x_1740_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_1741_ = l_Array_append___redArg(v___x_1740_, v_fst_1729_);
lean_dec(v_fst_1729_);
v___x_1742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1742_, 0, v_a_1723_);
lean_ctor_set(v___x_1742_, 1, v___x_1715_);
lean_ctor_set(v___x_1742_, 2, v___x_1741_);
v___x_1743_ = l_Lean_Syntax_node2(v_a_1723_, v___x_1717_, v___x_1739_, v___x_1742_);
v___x_1744_ = lean_array_push(v_a_1698_, v___x_1743_);
v___x_1745_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13));
v___x_1746_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14));
lean_inc_n(v_a_1725_, 35);
v___x_1747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_a_1725_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v_sz_1748_ = lean_array_size(v___x_1744_);
v___x_1749_ = ((size_t)0ULL);
v___x_1750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_1748_, v___x_1749_, v___x_1744_);
v___x_1751_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16);
v___x_1752_ = l_Lean_mkSepArray(v___x_1750_, v___x_1751_);
lean_dec_ref(v___x_1750_);
v___x_1753_ = l_Array_append___redArg(v___x_1740_, v___x_1752_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1754_, 0, v_a_1725_);
lean_ctor_set(v___x_1754_, 1, v___x_1715_);
lean_ctor_set(v___x_1754_, 2, v___x_1753_);
v___x_1755_ = l_Lean_Syntax_node1(v_a_1725_, v___x_1715_, v___x_1754_);
v___x_1756_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17));
v___x_1757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_a_1725_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19);
v___x_1759_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21));
lean_inc_n(v_currMacroScope_1701_, 5);
lean_inc_n(v_quotContext_1700_, 5);
v___x_1760_ = l_Lean_addMacroScope(v_quotContext_1700_, v___x_1759_, v_currMacroScope_1701_);
v___x_1761_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23));
v___x_1762_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1762_, 0, v_a_1725_);
lean_ctor_set(v___x_1762_, 1, v___x_1758_);
lean_ctor_set(v___x_1762_, 2, v___x_1760_);
lean_ctor_set(v___x_1762_, 3, v___x_1761_);
v___x_1763_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__7));
v___x_1764_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__9));
v___x_1765_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7));
v___x_1766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_a_1725_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__11));
v___x_1768_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__13);
v___x_1769_ = lean_box(0);
v___x_1770_ = l_Lean_addMacroScope(v_quotContext_1700_, v___x_1769_, v_currMacroScope_1701_);
v___x_1771_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27));
v___x_1772_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1772_, 0, v_a_1725_);
lean_ctor_set(v___x_1772_, 1, v___x_1768_);
lean_ctor_set(v___x_1772_, 2, v___x_1770_);
lean_ctor_set(v___x_1772_, 3, v___x_1771_);
v___x_1773_ = l_Lean_Syntax_node1(v_a_1725_, v___x_1767_, v___x_1772_);
v___x_1774_ = l_Lean_Syntax_node2(v_a_1725_, v___x_1764_, v___x_1766_, v___x_1773_);
v___x_1775_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__33, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__33_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__33);
v___x_1776_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__36));
v___x_1777_ = l_Lean_addMacroScope(v_quotContext_1700_, v___x_1776_, v_currMacroScope_1701_);
v___x_1778_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30));
v___x_1779_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1779_, 0, v_a_1725_);
lean_ctor_set(v___x_1779_, 1, v___x_1775_);
lean_ctor_set(v___x_1779_, 2, v___x_1777_);
lean_ctor_set(v___x_1779_, 3, v___x_1778_);
v___x_1780_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__43, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__43_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__43);
v___x_1781_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__45));
v___x_1782_ = l_Lean_addMacroScope(v_quotContext_1700_, v___x_1781_, v_currMacroScope_1701_);
v___x_1783_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33));
v___x_1784_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1784_, 0, v_a_1725_);
lean_ctor_set(v___x_1784_, 1, v___x_1780_);
lean_ctor_set(v___x_1784_, 2, v___x_1782_);
lean_ctor_set(v___x_1784_, 3, v___x_1783_);
v___x_1785_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35));
v___x_1786_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36));
v___x_1787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_a_1725_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38));
v___x_1789_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11);
v___x_1790_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12));
v___x_1791_ = l_Lean_addMacroScope(v_quotContext_1700_, v___x_1790_, v_currMacroScope_1701_);
v___x_1792_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1792_, 0, v_a_1725_);
lean_ctor_set(v___x_1792_, 1, v___x_1789_);
lean_ctor_set(v___x_1792_, 2, v___x_1791_);
lean_ctor_set(v___x_1792_, 3, v___x_1703_);
v___x_1793_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39));
v___x_1794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1794_, 0, v_a_1725_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6));
v___x_1796_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7));
v___x_1797_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1797_, 0, v_a_1725_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = l_Lean_Syntax_node1(v_a_1725_, v___x_1795_, v___x_1797_);
lean_inc_ref(v___x_1792_);
v___x_1799_ = l_Lean_Syntax_node3(v_a_1725_, v___x_1788_, v___x_1792_, v___x_1794_, v___x_1798_);
v___x_1800_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40));
v___x_1801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1801_, 0, v_a_1725_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42));
v___x_1803_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43));
v___x_1804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1804_, 0, v_a_1725_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = l_Lean_Syntax_node1(v_a_1725_, v___x_1802_, v___x_1804_);
v___x_1806_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44));
v___x_1807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1807_, 0, v_a_1725_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45));
v___x_1809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1809_, 0, v_a_1725_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = l_Lean_Syntax_node1(v_a_1725_, v___x_1802_, v___x_1809_);
v___x_1811_ = l_Lean_Syntax_node6(v_a_1725_, v___x_1785_, v___x_1787_, v___x_1799_, v___x_1801_, v___x_1805_, v___x_1807_, v___x_1810_);
v___x_1812_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23));
v___x_1813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1813_, 0, v_a_1725_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
lean_inc_ref_n(v___x_1813_, 3);
lean_inc_n(v___x_1774_, 3);
v___x_1814_ = l_Lean_Syntax_node3(v_a_1725_, v___x_1763_, v___x_1774_, v___x_1811_, v___x_1813_);
v___x_1815_ = l_Lean_Syntax_node3(v_a_1725_, v___x_1763_, v___x_1774_, v_snd_1730_, v___x_1813_);
v___x_1816_ = l_Lean_Syntax_node2(v_a_1725_, v___x_1715_, v___x_1814_, v___x_1815_);
v___x_1817_ = l_Lean_Syntax_node2(v_a_1725_, v___x_1717_, v___x_1784_, v___x_1816_);
v___x_1818_ = l_Lean_Syntax_node3(v_a_1725_, v___x_1763_, v___x_1774_, v___x_1817_, v___x_1813_);
v___x_1819_ = l_Lean_Syntax_node1(v_a_1725_, v___x_1715_, v___x_1818_);
v___x_1820_ = l_Lean_Syntax_node2(v_a_1725_, v___x_1717_, v___x_1779_, v___x_1819_);
v___x_1821_ = l_Lean_Syntax_node3(v_a_1725_, v___x_1763_, v___x_1774_, v___x_1820_, v___x_1813_);
v___x_1822_ = l_Lean_Syntax_node2(v_a_1725_, v___x_1715_, v___x_1821_, v___x_1792_);
v___x_1823_ = l_Lean_Syntax_node2(v_a_1725_, v___x_1717_, v___x_1762_, v___x_1822_);
v___x_1824_ = l_Lean_Syntax_node4(v_a_1725_, v___x_1745_, v___x_1747_, v___x_1755_, v___x_1757_, v___x_1823_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1824_);
v___x_1826_ = v___x_1727_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec(v_a_1723_);
lean_dec(v_a_1721_);
lean_dec(v_a_1698_);
lean_dec(v_head_1686_);
v_a_1831_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1724_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1724_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_a_1721_);
lean_dec(v_a_1698_);
lean_dec(v_head_1686_);
lean_dec_ref(v___f_1685_);
v_a_1839_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1722_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1722_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_a_1698_);
lean_dec(v_head_1686_);
lean_dec_ref(v___f_1685_);
v_a_1847_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1720_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1720_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_head_1686_);
lean_dec_ref(v___f_1685_);
lean_dec(v_auxFunName_1683_);
lean_dec(v_name_1682_);
lean_dec_ref(v_alts_1681_);
lean_dec(v___x_1680_);
v_a_1855_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1697_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1697_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_1863_ = _args[0];
lean_object* v___x_1864_ = _args[1];
lean_object* v_alts_1865_ = _args[2];
lean_object* v_name_1866_ = _args[3];
lean_object* v_auxFunName_1867_ = _args[4];
lean_object* v_header_1868_ = _args[5];
lean_object* v___f_1869_ = _args[6];
lean_object* v_head_1870_ = _args[7];
lean_object* v_xs_1871_ = _args[8];
lean_object* v_x_1872_ = _args[9];
lean_object* v___y_1873_ = _args[10];
lean_object* v___y_1874_ = _args[11];
lean_object* v___y_1875_ = _args[12];
lean_object* v___y_1876_ = _args[13];
lean_object* v___y_1877_ = _args[14];
lean_object* v___y_1878_ = _args[15];
lean_object* v___y_1879_ = _args[16];
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(v_indVal_1863_, v___x_1864_, v_alts_1865_, v_name_1866_, v_auxFunName_1867_, v_header_1868_, v___f_1869_, v_head_1870_, v_xs_1871_, v_x_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec_ref(v_x_1872_);
lean_dec_ref(v_xs_1871_);
lean_dec_ref(v_header_1868_);
lean_dec_ref(v_indVal_1863_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_ref_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v_ref_1888_ = lean_ctor_get(v___y_1885_, 5);
v___x_1889_ = 0;
v___x_1890_ = l_Lean_SourceInfo_fromRef(v_ref_1888_, v___x_1889_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed(lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(lean_object* v_indVal_1903_, lean_object* v_auxFunName_1904_, lean_object* v_header_1905_, lean_object* v_as_x27_1906_, lean_object* v_b_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
if (lean_obj_tag(v_as_x27_1906_) == 0)
{
lean_object* v___x_1915_; 
lean_dec_ref(v_header_1905_);
lean_dec(v_auxFunName_1904_);
lean_dec_ref(v_indVal_1903_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_b_1907_);
return v___x_1915_;
}
else
{
lean_object* v_head_1916_; lean_object* v_tail_1917_; lean_object* v___x_1918_; 
v_head_1916_ = lean_ctor_get(v_as_x27_1906_, 0);
v_tail_1917_ = lean_ctor_get(v_as_x27_1906_, 1);
lean_inc(v_head_1916_);
v___x_1918_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v_head_1916_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v_toConstantVal_1920_; lean_object* v_name_1921_; lean_object* v_type_1922_; lean_object* v___f_1923_; lean_object* v___x_1924_; lean_object* v_alts_1925_; lean_object* v___f_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1918_);
v_toConstantVal_1920_ = lean_ctor_get(v_a_1919_, 0);
lean_inc_ref(v_toConstantVal_1920_);
lean_dec(v_a_1919_);
v_name_1921_ = lean_ctor_get(v_toConstantVal_1920_, 0);
lean_inc(v_name_1921_);
v_type_1922_ = lean_ctor_get(v_toConstantVal_1920_, 2);
lean_inc_ref(v_type_1922_);
lean_dec_ref(v_toConstantVal_1920_);
v___f_1923_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0));
v___x_1924_ = lean_unsigned_to_nat(0u);
v_alts_1925_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
lean_inc(v_head_1916_);
lean_inc_ref(v_header_1905_);
lean_inc(v_auxFunName_1904_);
lean_inc_ref(v_indVal_1903_);
v___f_1926_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1926_, 0, v_indVal_1903_);
lean_closure_set(v___f_1926_, 1, v___x_1924_);
lean_closure_set(v___f_1926_, 2, v_alts_1925_);
lean_closure_set(v___f_1926_, 3, v_name_1921_);
lean_closure_set(v___f_1926_, 4, v_auxFunName_1904_);
lean_closure_set(v___f_1926_, 5, v_header_1905_);
lean_closure_set(v___f_1926_, 6, v___f_1923_);
lean_closure_set(v___f_1926_, 7, v_head_1916_);
v___x_1927_ = 0;
v___x_1928_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v_type_1922_, v___f_1926_, v___x_1927_, v___x_1927_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = lean_array_push(v_b_1907_, v_a_1929_);
v_as_x27_1906_ = v_tail_1917_;
v_b_1907_ = v___x_1930_;
goto _start;
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v_b_1907_);
lean_dec_ref(v_header_1905_);
lean_dec(v_auxFunName_1904_);
lean_dec_ref(v_indVal_1903_);
v_a_1932_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1928_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1928_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec_ref(v_b_1907_);
lean_dec_ref(v_header_1905_);
lean_dec(v_auxFunName_1904_);
lean_dec_ref(v_indVal_1903_);
v_a_1940_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1918_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1918_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___boxed(lean_object* v_indVal_1948_, lean_object* v_auxFunName_1949_, lean_object* v_header_1950_, lean_object* v_as_x27_1951_, lean_object* v_b_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_1948_, v_auxFunName_1949_, v_header_1950_, v_as_x27_1951_, v_b_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v_as_x27_1951_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(size_t v_sz_1961_, size_t v_i_1962_, lean_object* v_bs_1963_){
_start:
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_usize_dec_lt(v_i_1962_, v_sz_1961_);
if (v___x_1964_ == 0)
{
return v_bs_1963_;
}
else
{
lean_object* v_v_1965_; lean_object* v___x_1966_; lean_object* v_bs_x27_1967_; size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v_v_1965_ = lean_array_uget(v_bs_1963_, v_i_1962_);
v___x_1966_ = lean_unsigned_to_nat(0u);
v_bs_x27_1967_ = lean_array_uset(v_bs_1963_, v_i_1962_, v___x_1966_);
v___x_1968_ = ((size_t)1ULL);
v___x_1969_ = lean_usize_add(v_i_1962_, v___x_1968_);
v___x_1970_ = lean_array_uset(v_bs_x27_1967_, v_i_1962_, v_v_1965_);
v_i_1962_ = v___x_1969_;
v_bs_1963_ = v___x_1970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4___boxed(lean_object* v_sz_1972_, lean_object* v_i_1973_, lean_object* v_bs_1974_){
_start:
{
size_t v_sz_boxed_1975_; size_t v_i_boxed_1976_; lean_object* v_res_1977_; 
v_sz_boxed_1975_ = lean_unbox_usize(v_sz_1972_);
lean_dec(v_sz_1972_);
v_i_boxed_1976_ = lean_unbox_usize(v_i_1973_);
lean_dec(v_i_1973_);
v_res_1977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(v_sz_boxed_1975_, v_i_boxed_1976_, v_bs_1974_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(lean_object* v_header_1978_, lean_object* v_indVal_1979_, lean_object* v_auxFunName_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_ctors_1988_; lean_object* v_alts_1989_; lean_object* v___x_1990_; 
v_ctors_1988_ = lean_ctor_get(v_indVal_1979_, 4);
lean_inc(v_ctors_1988_);
v_alts_1989_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_1990_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_1979_, v_auxFunName_1980_, v_header_1978_, v_ctors_1988_, v_alts_1989_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
lean_dec(v_ctors_1988_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2001_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2001_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2001_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
size_t v_sz_1995_; size_t v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
v_sz_1995_ = lean_array_size(v_a_1991_);
v___x_1996_ = ((size_t)0ULL);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(v_sz_1995_, v___x_1996_, v_a_1991_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1997_);
v___x_1999_ = v___x_1993_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts___boxed(lean_object* v_header_2002_, lean_object* v_indVal_2003_, lean_object* v_auxFunName_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(v_header_2002_, v_indVal_2003_, v_auxFunName_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(lean_object* v_upperBound_2013_, lean_object* v_xs_2014_, lean_object* v_indVal_2015_, lean_object* v_auxFunName_2016_, lean_object* v_header_2017_, lean_object* v_inst_2018_, lean_object* v_R_2019_, lean_object* v_a_2020_, lean_object* v_b_2021_, lean_object* v_c_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v_upperBound_2013_, v_xs_2014_, v_indVal_2015_, v_auxFunName_2016_, v_header_2017_, v_a_2020_, v_b_2021_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2031_ = _args[0];
lean_object* v_xs_2032_ = _args[1];
lean_object* v_indVal_2033_ = _args[2];
lean_object* v_auxFunName_2034_ = _args[3];
lean_object* v_header_2035_ = _args[4];
lean_object* v_inst_2036_ = _args[5];
lean_object* v_R_2037_ = _args[6];
lean_object* v_a_2038_ = _args[7];
lean_object* v_b_2039_ = _args[8];
lean_object* v_c_2040_ = _args[9];
lean_object* v___y_2041_ = _args[10];
lean_object* v___y_2042_ = _args[11];
lean_object* v___y_2043_ = _args[12];
lean_object* v___y_2044_ = _args[13];
lean_object* v___y_2045_ = _args[14];
lean_object* v___y_2046_ = _args[15];
lean_object* v___y_2047_ = _args[16];
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(v_upperBound_2031_, v_xs_2032_, v_indVal_2033_, v_auxFunName_2034_, v_header_2035_, v_inst_2036_, v_R_2037_, v_a_2038_, v_b_2039_, v_c_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v_header_2035_);
lean_dec_ref(v_indVal_2033_);
lean_dec_ref(v_xs_2032_);
lean_dec(v_upperBound_2031_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(lean_object* v_upperBound_2049_, lean_object* v_inst_2050_, lean_object* v_R_2051_, lean_object* v_a_2052_, lean_object* v_b_2053_, lean_object* v_c_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_2049_, v_a_2052_, v_b_2053_, v___y_2059_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___boxed(lean_object* v_upperBound_2063_, lean_object* v_inst_2064_, lean_object* v_R_2065_, lean_object* v_a_2066_, lean_object* v_b_2067_, lean_object* v_c_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(v_upperBound_2063_, v_inst_2064_, v_R_2065_, v_a_2066_, v_b_2067_, v_c_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v_upperBound_2063_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(lean_object* v_indVal_2077_, lean_object* v_auxFunName_2078_, lean_object* v_header_2079_, lean_object* v_as_2080_, lean_object* v_as_x27_2081_, lean_object* v_b_2082_, lean_object* v_a_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_2077_, v_auxFunName_2078_, v_header_2079_, v_as_x27_2081_, v_b_2082_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___boxed(lean_object* v_indVal_2092_, lean_object* v_auxFunName_2093_, lean_object* v_header_2094_, lean_object* v_as_2095_, lean_object* v_as_x27_2096_, lean_object* v_b_2097_, lean_object* v_a_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(v_indVal_2092_, v_auxFunName_2093_, v_header_2094_, v_as_2095_, v_as_x27_2096_, v_b_2097_, v_a_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v_as_x27_2096_);
lean_dec(v_as_2095_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct(lean_object* v_header_2120_, lean_object* v_indVal_2121_, lean_object* v_auxFunName_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v___x_2130_; 
lean_inc_ref(v_indVal_2121_);
lean_inc_ref(v_header_2120_);
v___x_2130_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2120_, v_indVal_2121_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref(v___x_2130_);
v___x_2132_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(v_header_2120_, v_indVal_2121_, v_auxFunName_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2163_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2163_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2163_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_ref_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; size_t v_sz_2146_; size_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v_ref_2137_ = lean_ctor_get(v_a_2127_, 5);
v___x_2138_ = 0;
v___x_2139_ = l_Lean_SourceInfo_fromRef(v_ref_2137_, v___x_2138_);
v___x_2140_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0));
v___x_2141_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1));
lean_inc_n(v___x_2139_, 6);
v___x_2142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2139_);
lean_ctor_set(v___x_2142_, 1, v___x_2140_);
v___x_2143_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2144_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_2145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2139_);
lean_ctor_set(v___x_2145_, 1, v___x_2143_);
lean_ctor_set(v___x_2145_, 2, v___x_2144_);
v_sz_2146_ = lean_array_size(v_a_2131_);
v___x_2147_ = ((size_t)0ULL);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_2146_, v___x_2147_, v_a_2131_);
v___x_2149_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16);
v___x_2150_ = l_Lean_mkSepArray(v___x_2148_, v___x_2149_);
lean_dec_ref(v___x_2148_);
v___x_2151_ = l_Array_append___redArg(v___x_2144_, v___x_2150_);
lean_dec_ref(v___x_2150_);
v___x_2152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2139_);
lean_ctor_set(v___x_2152_, 1, v___x_2143_);
lean_ctor_set(v___x_2152_, 2, v___x_2151_);
v___x_2153_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2));
v___x_2154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2139_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4));
v___x_2156_ = l_Array_append___redArg(v___x_2144_, v_a_2133_);
lean_dec(v_a_2133_);
v___x_2157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2139_);
lean_ctor_set(v___x_2157_, 1, v___x_2143_);
lean_ctor_set(v___x_2157_, 2, v___x_2156_);
v___x_2158_ = l_Lean_Syntax_node1(v___x_2139_, v___x_2155_, v___x_2157_);
lean_inc_ref(v___x_2145_);
v___x_2159_ = l_Lean_Syntax_node6(v___x_2139_, v___x_2141_, v___x_2142_, v___x_2145_, v___x_2145_, v___x_2152_, v___x_2154_, v___x_2158_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2159_);
v___x_2161_ = v___x_2135_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_a_2131_);
v_a_2164_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2132_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2132_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_auxFunName_2122_);
lean_dec_ref(v_indVal_2121_);
lean_dec_ref(v_header_2120_);
v_a_2172_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2130_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2130_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___boxed(lean_object* v_header_2180_, lean_object* v_indVal_2181_, lean_object* v_auxFunName_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(v_header_2180_, v_indVal_2181_, v_auxFunName_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody(lean_object* v_header_2191_, lean_object* v_indVal_2192_, lean_object* v_auxFunName_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v___x_2201_; lean_object* v_toConstantVal_2202_; lean_object* v_env_2203_; lean_object* v_name_2204_; uint8_t v___x_2205_; 
v___x_2201_ = lean_st_ref_get(v_a_2199_);
v_toConstantVal_2202_ = lean_ctor_get(v_indVal_2192_, 0);
v_env_2203_ = lean_ctor_get(v___x_2201_, 0);
lean_inc_ref(v_env_2203_);
lean_dec(v___x_2201_);
v_name_2204_ = lean_ctor_get(v_toConstantVal_2202_, 0);
lean_inc(v_name_2204_);
v___x_2205_ = l_Lean_isStructure(v_env_2203_, v_name_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(v_header_2191_, v_indVal_2192_, v_auxFunName_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
return v___x_2206_;
}
else
{
lean_object* v___x_2207_; 
lean_dec(v_auxFunName_2193_);
v___x_2207_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(v_header_2191_, v_indVal_2192_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
lean_dec_ref(v_header_2191_);
return v___x_2207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody___boxed(lean_object* v_header_2208_, lean_object* v_indVal_2209_, lean_object* v_auxFunName_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_Elab_Deriving_Repr_mkBody(v_header_2208_, v_indVal_2209_, v_auxFunName_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
return v_res_2218_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15));
v___x_2260_ = l_String_toRawSubstring_x27(v___x_2259_);
return v___x_2260_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__34));
v___x_2290_ = l_String_toRawSubstring_x27(v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction(lean_object* v_ctx_2327_, lean_object* v_i_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v_typeInfos_2336_; lean_object* v_auxFunNames_2337_; uint8_t v_usePartial_2338_; lean_object* v___x_2339_; lean_object* v_indVal_2340_; lean_object* v___x_2341_; 
v_typeInfos_2336_ = lean_ctor_get(v_ctx_2327_, 1);
v_auxFunNames_2337_ = lean_ctor_get(v_ctx_2327_, 2);
v_usePartial_2338_ = lean_ctor_get_uint8(v_ctx_2327_, sizeof(void*)*3);
v___x_2339_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_2340_ = lean_array_get_borrowed(v___x_2339_, v_typeInfos_2336_, v_i_2328_);
lean_inc(v_indVal_2340_);
v___x_2341_ = l_Lean_Elab_Deriving_Repr_mkReprHeader(v_indVal_2340_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2514_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2514_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2514_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; lean_object* v_auxFunName_2347_; lean_object* v_body_2349_; lean_object* v___y_2350_; lean_object* v___x_2497_; 
v___x_2346_ = lean_box(0);
v_auxFunName_2347_ = lean_array_get_borrowed(v___x_2346_, v_auxFunNames_2337_, v_i_2328_);
lean_inc(v_auxFunName_2347_);
lean_inc(v_indVal_2340_);
lean_inc(v_a_2342_);
v___x_2497_ = l_Lean_Elab_Deriving_Repr_mkBody(v_a_2342_, v_indVal_2340_, v_auxFunName_2347_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
if (lean_obj_tag(v___x_2497_) == 0)
{
if (v_usePartial_2338_ == 0)
{
lean_object* v_a_2498_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref(v___x_2497_);
v_body_2349_ = v_a_2498_;
v___y_2350_ = v_a_2333_;
goto v___jp_2348_;
}
else
{
lean_object* v_a_2499_; lean_object* v_argNames_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v_a_2499_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2499_);
lean_dec_ref(v___x_2497_);
v_argNames_2500_ = lean_ctor_get(v_a_2342_, 1);
v___x_2501_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
lean_inc_ref(v_argNames_2500_);
v___x_2502_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2327_, v___x_2501_, v_argNames_2500_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2504_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref(v___x_2502_);
v___x_2504_ = l_Lean_Elab_Deriving_mkLet(v_a_2503_, v_a_2499_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
lean_dec(v_a_2503_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref(v___x_2504_);
v_body_2349_ = v_a_2505_;
v___y_2350_ = v_a_2333_;
goto v___jp_2348_;
}
else
{
lean_del_object(v___x_2344_);
lean_dec(v_a_2342_);
return v___x_2504_;
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_a_2499_);
lean_del_object(v___x_2344_);
lean_dec(v_a_2342_);
v_a_2506_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2502_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2502_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
else
{
lean_del_object(v___x_2344_);
lean_dec(v_a_2342_);
return v___x_2497_;
}
v___jp_2348_:
{
if (v_usePartial_2338_ == 0)
{
lean_object* v_binders_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2417_; 
v_binders_2351_ = lean_ctor_get(v_a_2342_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_a_2342_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; lean_object* v_unused_2419_; lean_object* v_unused_2420_; 
v_unused_2418_ = lean_ctor_get(v_a_2342_, 3);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_a_2342_, 2);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_a_2342_, 1);
lean_dec(v_unused_2420_);
v___x_2353_ = v_a_2342_;
v_isShared_2354_ = v_isSharedCheck_2417_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_binders_2351_);
lean_dec(v_a_2342_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2417_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_ref_2355_; lean_object* v_quotContext_2356_; lean_object* v_currMacroScope_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v_ref_2355_ = lean_ctor_get(v___y_2350_, 5);
v_quotContext_2356_ = lean_ctor_get(v___y_2350_, 10);
v_currMacroScope_2357_ = lean_ctor_get(v___y_2350_, 11);
v___x_2358_ = l_Lean_SourceInfo_fromRef(v_ref_2355_, v_usePartial_2338_);
v___x_2359_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2));
v___x_2360_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4));
v___x_2361_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2362_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
lean_inc_n(v___x_2358_, 4);
v___x_2363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2358_);
lean_ctor_set(v___x_2363_, 1, v___x_2361_);
lean_ctor_set(v___x_2363_, 2, v___x_2362_);
v___x_2364_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6));
v___x_2365_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7));
v___x_2366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2358_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9));
v___x_2368_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11));
lean_inc_ref(v___x_2363_);
v___x_2369_ = l_Lean_Syntax_node1(v___x_2358_, v___x_2368_, v___x_2363_);
v___x_2370_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14));
v___x_2371_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16);
v___x_2372_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17));
lean_inc(v_currMacroScope_2357_);
lean_inc(v_quotContext_2356_);
v___x_2373_ = l_Lean_addMacroScope(v_quotContext_2356_, v___x_2372_, v_currMacroScope_2357_);
v___x_2374_ = lean_box(0);
if (v_isShared_2354_ == 0)
{
lean_ctor_set_tag(v___x_2353_, 3);
lean_ctor_set(v___x_2353_, 3, v___x_2374_);
lean_ctor_set(v___x_2353_, 2, v___x_2373_);
lean_ctor_set(v___x_2353_, 1, v___x_2371_);
lean_ctor_set(v___x_2353_, 0, v___x_2358_);
v___x_2376_ = v___x_2353_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2416_, 2, v___x_2373_);
lean_ctor_set(v_reuseFailAlloc_2416_, 3, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
lean_inc_ref_n(v___x_2363_, 11);
lean_inc_n(v___x_2358_, 19);
v___x_2377_ = l_Lean_Syntax_node2(v___x_2358_, v___x_2370_, v___x_2376_, v___x_2363_);
v___x_2378_ = l_Lean_Syntax_node2(v___x_2358_, v___x_2367_, v___x_2369_, v___x_2377_);
v___x_2379_ = l_Lean_Syntax_node1(v___x_2358_, v___x_2361_, v___x_2378_);
v___x_2380_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18));
v___x_2381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2358_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = l_Lean_Syntax_node3(v___x_2358_, v___x_2364_, v___x_2366_, v___x_2379_, v___x_2381_);
v___x_2383_ = l_Lean_Syntax_node1(v___x_2358_, v___x_2361_, v___x_2382_);
v___x_2384_ = l_Lean_Syntax_node7(v___x_2358_, v___x_2360_, v___x_2363_, v___x_2383_, v___x_2363_, v___x_2363_, v___x_2363_, v___x_2363_, v___x_2363_);
v___x_2385_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20));
v___x_2386_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21));
v___x_2387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2358_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23));
lean_inc(v_auxFunName_2347_);
v___x_2389_ = lean_mk_syntax_ident(v_auxFunName_2347_);
v___x_2390_ = l_Lean_Syntax_node2(v___x_2358_, v___x_2388_, v___x_2389_, v___x_2363_);
v___x_2391_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25));
v___x_2392_ = l_Array_append___redArg(v___x_2362_, v_binders_2351_);
lean_dec_ref(v_binders_2351_);
v___x_2393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2358_);
lean_ctor_set(v___x_2393_, 1, v___x_2361_);
lean_ctor_set(v___x_2393_, 2, v___x_2392_);
v___x_2394_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27));
v___x_2395_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13));
v___x_2396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2358_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28);
v___x_2398_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29));
lean_inc(v_currMacroScope_2357_);
lean_inc(v_quotContext_2356_);
v___x_2399_ = l_Lean_addMacroScope(v_quotContext_2356_, v___x_2398_, v_currMacroScope_2357_);
v___x_2400_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34));
v___x_2401_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2358_);
lean_ctor_set(v___x_2401_, 1, v___x_2397_);
lean_ctor_set(v___x_2401_, 2, v___x_2399_);
lean_ctor_set(v___x_2401_, 3, v___x_2400_);
v___x_2402_ = l_Lean_Syntax_node2(v___x_2358_, v___x_2394_, v___x_2396_, v___x_2401_);
v___x_2403_ = l_Lean_Syntax_node1(v___x_2358_, v___x_2361_, v___x_2402_);
v___x_2404_ = l_Lean_Syntax_node2(v___x_2358_, v___x_2391_, v___x_2393_, v___x_2403_);
v___x_2405_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36));
v___x_2406_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37));
v___x_2407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2358_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40));
v___x_2409_ = l_Lean_Syntax_node2(v___x_2358_, v___x_2408_, v___x_2363_, v___x_2363_);
v___x_2410_ = l_Lean_Syntax_node4(v___x_2358_, v___x_2405_, v___x_2407_, v_body_2349_, v___x_2409_, v___x_2363_);
v___x_2411_ = l_Lean_Syntax_node5(v___x_2358_, v___x_2385_, v___x_2387_, v___x_2390_, v___x_2404_, v___x_2410_, v___x_2363_);
v___x_2412_ = l_Lean_Syntax_node2(v___x_2358_, v___x_2359_, v___x_2384_, v___x_2411_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2412_);
v___x_2414_ = v___x_2344_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v_binders_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2493_; 
v_binders_2421_ = lean_ctor_get(v_a_2342_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_a_2342_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; lean_object* v_unused_2495_; lean_object* v_unused_2496_; 
v_unused_2494_ = lean_ctor_get(v_a_2342_, 3);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v_a_2342_, 2);
lean_dec(v_unused_2495_);
v_unused_2496_ = lean_ctor_get(v_a_2342_, 1);
lean_dec(v_unused_2496_);
v___x_2423_ = v_a_2342_;
v_isShared_2424_ = v_isSharedCheck_2493_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_binders_2421_);
lean_dec(v_a_2342_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2493_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v_ref_2425_; lean_object* v_quotContext_2426_; lean_object* v_currMacroScope_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
v_ref_2425_ = lean_ctor_get(v___y_2350_, 5);
v_quotContext_2426_ = lean_ctor_get(v___y_2350_, 10);
v_currMacroScope_2427_ = lean_ctor_get(v___y_2350_, 11);
v___x_2428_ = 0;
v___x_2429_ = l_Lean_SourceInfo_fromRef(v_ref_2425_, v___x_2428_);
v___x_2430_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2));
v___x_2431_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4));
v___x_2432_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2433_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
lean_inc_n(v___x_2429_, 4);
v___x_2434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2429_);
lean_ctor_set(v___x_2434_, 1, v___x_2432_);
lean_ctor_set(v___x_2434_, 2, v___x_2433_);
v___x_2435_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6));
v___x_2436_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7));
v___x_2437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2429_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9));
v___x_2439_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11));
lean_inc_ref(v___x_2434_);
v___x_2440_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2439_, v___x_2434_);
v___x_2441_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14));
v___x_2442_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16);
v___x_2443_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17));
lean_inc(v_currMacroScope_2427_);
lean_inc(v_quotContext_2426_);
v___x_2444_ = l_Lean_addMacroScope(v_quotContext_2426_, v___x_2443_, v_currMacroScope_2427_);
v___x_2445_ = lean_box(0);
if (v_isShared_2424_ == 0)
{
lean_ctor_set_tag(v___x_2423_, 3);
lean_ctor_set(v___x_2423_, 3, v___x_2445_);
lean_ctor_set(v___x_2423_, 2, v___x_2444_);
lean_ctor_set(v___x_2423_, 1, v___x_2442_);
lean_ctor_set(v___x_2423_, 0, v___x_2429_);
v___x_2447_ = v___x_2423_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
lean_inc_ref_n(v___x_2434_, 10);
lean_inc_n(v___x_2429_, 22);
v___x_2448_ = l_Lean_Syntax_node2(v___x_2429_, v___x_2441_, v___x_2447_, v___x_2434_);
v___x_2449_ = l_Lean_Syntax_node2(v___x_2429_, v___x_2438_, v___x_2440_, v___x_2448_);
v___x_2450_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2432_, v___x_2449_);
v___x_2451_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18));
v___x_2452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2429_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = l_Lean_Syntax_node3(v___x_2429_, v___x_2435_, v___x_2437_, v___x_2450_, v___x_2452_);
v___x_2454_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2432_, v___x_2453_);
v___x_2455_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41));
v___x_2456_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42));
v___x_2457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2429_);
lean_ctor_set(v___x_2457_, 1, v___x_2455_);
v___x_2458_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2456_, v___x_2457_);
v___x_2459_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2432_, v___x_2458_);
v___x_2460_ = l_Lean_Syntax_node7(v___x_2429_, v___x_2431_, v___x_2434_, v___x_2454_, v___x_2434_, v___x_2434_, v___x_2434_, v___x_2434_, v___x_2459_);
v___x_2461_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20));
v___x_2462_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21));
v___x_2463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2429_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23));
lean_inc(v_auxFunName_2347_);
v___x_2465_ = lean_mk_syntax_ident(v_auxFunName_2347_);
v___x_2466_ = l_Lean_Syntax_node2(v___x_2429_, v___x_2464_, v___x_2465_, v___x_2434_);
v___x_2467_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25));
v___x_2468_ = l_Array_append___redArg(v___x_2433_, v_binders_2421_);
lean_dec_ref(v_binders_2421_);
v___x_2469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2429_);
lean_ctor_set(v___x_2469_, 1, v___x_2432_);
lean_ctor_set(v___x_2469_, 2, v___x_2468_);
v___x_2470_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27));
v___x_2471_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13));
v___x_2472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2429_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28);
v___x_2474_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29));
lean_inc(v_currMacroScope_2427_);
lean_inc(v_quotContext_2426_);
v___x_2475_ = l_Lean_addMacroScope(v_quotContext_2426_, v___x_2474_, v_currMacroScope_2427_);
v___x_2476_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34));
v___x_2477_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2429_);
lean_ctor_set(v___x_2477_, 1, v___x_2473_);
lean_ctor_set(v___x_2477_, 2, v___x_2475_);
lean_ctor_set(v___x_2477_, 3, v___x_2476_);
v___x_2478_ = l_Lean_Syntax_node2(v___x_2429_, v___x_2470_, v___x_2472_, v___x_2477_);
v___x_2479_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2432_, v___x_2478_);
v___x_2480_ = l_Lean_Syntax_node2(v___x_2429_, v___x_2467_, v___x_2469_, v___x_2479_);
v___x_2481_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36));
v___x_2482_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37));
v___x_2483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2429_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40));
v___x_2485_ = l_Lean_Syntax_node2(v___x_2429_, v___x_2484_, v___x_2434_, v___x_2434_);
v___x_2486_ = l_Lean_Syntax_node4(v___x_2429_, v___x_2481_, v___x_2483_, v_body_2349_, v___x_2485_, v___x_2434_);
v___x_2487_ = l_Lean_Syntax_node5(v___x_2429_, v___x_2461_, v___x_2463_, v___x_2466_, v___x_2480_, v___x_2486_, v___x_2434_);
v___x_2488_ = l_Lean_Syntax_node2(v___x_2429_, v___x_2430_, v___x_2460_, v___x_2487_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2488_);
v___x_2490_ = v___x_2344_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
v_a_2515_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2341_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2341_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___boxed(lean_object* v_ctx_2523_, lean_object* v_i_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction(v_ctx_2523_, v_i_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_i_2524_);
lean_dec_ref(v_ctx_2523_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_2533_, lean_object* v_ctx_2534_, lean_object* v_a_2535_, lean_object* v_b_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
uint8_t v___x_2544_; 
v___x_2544_ = lean_nat_dec_lt(v_a_2535_, v_upperBound_2533_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; 
lean_dec(v_a_2535_);
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_b_2536_);
return v___x_2545_;
}
else
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction(v_ctx_2534_, v_a_2535_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = lean_array_push(v_b_2536_, v_a_2547_);
v___x_2549_ = lean_unsigned_to_nat(1u);
v___x_2550_ = lean_nat_add(v_a_2535_, v___x_2549_);
lean_dec(v_a_2535_);
v_a_2535_ = v___x_2550_;
v_b_2536_ = v___x_2548_;
goto _start;
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec_ref(v_b_2536_);
lean_dec(v_a_2535_);
v_a_2552_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2546_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2546_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_2560_, lean_object* v_ctx_2561_, lean_object* v_a_2562_, lean_object* v_b_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v_upperBound_2560_, v_ctx_2561_, v_a_2562_, v_b_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v_ctx_2561_);
lean_dec(v_upperBound_2560_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock(lean_object* v_ctx_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v_typeInfos_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v_auxDefs_2590_; lean_object* v___x_2591_; 
v_typeInfos_2587_ = lean_ctor_get(v_ctx_2579_, 1);
v___x_2588_ = lean_array_get_size(v_typeInfos_2587_);
v___x_2589_ = lean_unsigned_to_nat(0u);
v_auxDefs_2590_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_2591_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v___x_2588_, v_ctx_2579_, v___x_2589_, v_auxDefs_2590_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2612_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2612_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2612_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_ref_2596_; uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2610_; 
v_ref_2596_ = lean_ctor_get(v_a_2584_, 5);
v___x_2597_ = 0;
v___x_2598_ = l_Lean_SourceInfo_fromRef(v_ref_2596_, v___x_2597_);
v___x_2599_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0));
v___x_2600_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1));
lean_inc_n(v___x_2598_, 3);
v___x_2601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2598_);
lean_ctor_set(v___x_2601_, 1, v___x_2599_);
v___x_2602_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2603_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_2604_ = l_Array_append___redArg(v___x_2603_, v_a_2592_);
lean_dec(v_a_2592_);
v___x_2605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2598_);
lean_ctor_set(v___x_2605_, 1, v___x_2602_);
lean_ctor_set(v___x_2605_, 2, v___x_2604_);
v___x_2606_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2));
v___x_2607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2598_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = l_Lean_Syntax_node3(v___x_2598_, v___x_2600_, v___x_2601_, v___x_2605_, v___x_2607_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2608_);
v___x_2610_ = v___x_2594_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
v_a_2613_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2591_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2591_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___boxed(lean_object* v_ctx_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock(v_ctx_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec_ref(v_ctx_2621_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(lean_object* v_upperBound_2630_, lean_object* v_ctx_2631_, lean_object* v_inst_2632_, lean_object* v_R_2633_, lean_object* v_a_2634_, lean_object* v_b_2635_, lean_object* v_c_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v_upperBound_2630_, v_ctx_2631_, v_a_2634_, v_b_2635_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_2645_, lean_object* v_ctx_2646_, lean_object* v_inst_2647_, lean_object* v_R_2648_, lean_object* v_a_2649_, lean_object* v_b_2650_, lean_object* v_c_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(v_upperBound_2645_, v_ctx_2646_, v_inst_2647_, v_R_2648_, v_a_2649_, v_b_2650_, v_c_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec_ref(v_ctx_2646_);
lean_dec(v_upperBound_2645_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
if (lean_obj_tag(v_a_2660_) == 0)
{
lean_object* v___x_2662_; 
v___x_2662_ = l_List_reverse___redArg(v_a_2661_);
return v___x_2662_;
}
else
{
lean_object* v_head_2663_; lean_object* v_tail_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2673_; 
v_head_2663_ = lean_ctor_get(v_a_2660_, 0);
v_tail_2664_ = lean_ctor_get(v_a_2660_, 1);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_a_2660_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2666_ = v_a_2660_;
v_isShared_2667_ = v_isSharedCheck_2673_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_tail_2664_);
lean_inc(v_head_2663_);
lean_dec(v_a_2660_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2673_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = l_Lean_MessageData_ofSyntax(v_head_2663_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v_a_2661_);
lean_ctor_set(v___x_2666_, 0, v___x_2668_);
v___x_2670_ = v___x_2666_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_a_2661_);
v___x_2670_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
v_a_2660_ = v_tail_2664_;
v_a_2661_ = v___x_2670_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2674_; double v___x_2675_; 
v___x_2674_ = lean_unsigned_to_nat(0u);
v___x_2675_ = lean_float_of_nat(v___x_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(lean_object* v_cls_2678_, lean_object* v_msg_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v_ref_2685_; lean_object* v___x_2686_; lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2731_; 
v_ref_2685_ = lean_ctor_get(v___y_2682_, 5);
v___x_2686_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_spec__3(v_msg_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2689_ = v___x_2686_;
v_isShared_2690_ = v_isSharedCheck_2731_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2686_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2731_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; lean_object* v_traceState_2692_; lean_object* v_env_2693_; lean_object* v_nextMacroScope_2694_; lean_object* v_ngen_2695_; lean_object* v_auxDeclNGen_2696_; lean_object* v_cache_2697_; lean_object* v_messages_2698_; lean_object* v_infoState_2699_; lean_object* v_snapshotTasks_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2730_; 
v___x_2691_ = lean_st_ref_take(v___y_2683_);
v_traceState_2692_ = lean_ctor_get(v___x_2691_, 4);
v_env_2693_ = lean_ctor_get(v___x_2691_, 0);
v_nextMacroScope_2694_ = lean_ctor_get(v___x_2691_, 1);
v_ngen_2695_ = lean_ctor_get(v___x_2691_, 2);
v_auxDeclNGen_2696_ = lean_ctor_get(v___x_2691_, 3);
v_cache_2697_ = lean_ctor_get(v___x_2691_, 5);
v_messages_2698_ = lean_ctor_get(v___x_2691_, 6);
v_infoState_2699_ = lean_ctor_get(v___x_2691_, 7);
v_snapshotTasks_2700_ = lean_ctor_get(v___x_2691_, 8);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2702_ = v___x_2691_;
v_isShared_2703_ = v_isSharedCheck_2730_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_snapshotTasks_2700_);
lean_inc(v_infoState_2699_);
lean_inc(v_messages_2698_);
lean_inc(v_cache_2697_);
lean_inc(v_traceState_2692_);
lean_inc(v_auxDeclNGen_2696_);
lean_inc(v_ngen_2695_);
lean_inc(v_nextMacroScope_2694_);
lean_inc(v_env_2693_);
lean_dec(v___x_2691_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2730_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
uint64_t v_tid_2704_; lean_object* v_traces_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2729_; 
v_tid_2704_ = lean_ctor_get_uint64(v_traceState_2692_, sizeof(void*)*1);
v_traces_2705_ = lean_ctor_get(v_traceState_2692_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_traceState_2692_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2707_ = v_traceState_2692_;
v_isShared_2708_ = v_isSharedCheck_2729_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_traces_2705_);
lean_dec(v_traceState_2692_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2729_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; double v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2709_ = lean_box(0);
v___x_2710_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0);
v___x_2711_ = 0;
v___x_2712_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__12));
v___x_2713_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2713_, 0, v_cls_2678_);
lean_ctor_set(v___x_2713_, 1, v___x_2709_);
lean_ctor_set(v___x_2713_, 2, v___x_2712_);
lean_ctor_set_float(v___x_2713_, sizeof(void*)*3, v___x_2710_);
lean_ctor_set_float(v___x_2713_, sizeof(void*)*3 + 8, v___x_2710_);
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*3 + 16, v___x_2711_);
v___x_2714_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1));
v___x_2715_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v_a_2687_);
lean_ctor_set(v___x_2715_, 2, v___x_2714_);
lean_inc(v_ref_2685_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v_ref_2685_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = l_Lean_PersistentArray_push___redArg(v_traces_2705_, v___x_2716_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2717_);
v___x_2719_ = v___x_2707_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2717_);
lean_ctor_set_uint64(v_reuseFailAlloc_2728_, sizeof(void*)*1, v_tid_2704_);
v___x_2719_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2721_; 
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 4, v___x_2719_);
v___x_2721_ = v___x_2702_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_env_2693_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_nextMacroScope_2694_);
lean_ctor_set(v_reuseFailAlloc_2727_, 2, v_ngen_2695_);
lean_ctor_set(v_reuseFailAlloc_2727_, 3, v_auxDeclNGen_2696_);
lean_ctor_set(v_reuseFailAlloc_2727_, 4, v___x_2719_);
lean_ctor_set(v_reuseFailAlloc_2727_, 5, v_cache_2697_);
lean_ctor_set(v_reuseFailAlloc_2727_, 6, v_messages_2698_);
lean_ctor_set(v_reuseFailAlloc_2727_, 7, v_infoState_2699_);
lean_ctor_set(v_reuseFailAlloc_2727_, 8, v_snapshotTasks_2700_);
v___x_2721_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2722_ = lean_st_ref_set(v___y_2683_, v___x_2721_);
v___x_2723_ = lean_box(0);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v___x_2723_);
v___x_2725_ = v___x_2689_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___boxed(lean_object* v_cls_2732_, lean_object* v_msg_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v_cls_2732_, v_msg_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2739_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_2748_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2));
v___x_2749_ = l_Lean_Name_append(v___x_2748_, v___x_2747_);
return v___x_2749_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4));
v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(lean_object* v_declName_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; lean_object* v___x_2764_; 
v___x_2761_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
v___x_2762_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___lam__1___closed__51));
v___x_2763_ = 1;
lean_inc(v_declName_2753_);
v___x_2764_ = l_Lean_Elab_Deriving_mkContext(v___x_2761_, v___x_2762_, v_declName_2753_, v___x_2763_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref(v___x_2764_);
v___x_2766_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock(v_a_2765_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref(v___x_2766_);
v___x_2768_ = lean_unsigned_to_nat(1u);
v___x_2769_ = lean_mk_empty_array_with_capacity(v___x_2768_);
lean_inc_ref(v___x_2769_);
v___x_2770_ = lean_array_push(v___x_2769_, v_declName_2753_);
v___x_2771_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_2765_, v___x_2761_, v___x_2770_, v___x_2763_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
lean_dec_ref(v___x_2770_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_options_2772_; lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2813_; 
v_options_2772_ = lean_ctor_get(v_a_2758_, 2);
v_a_2773_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2775_ = v___x_2771_;
v_isShared_2776_ = v_isSharedCheck_2813_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2771_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2813_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v_inheritedTraceOptions_2777_; uint8_t v_hasTrace_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_inheritedTraceOptions_2777_ = lean_ctor_get(v_a_2758_, 13);
v_hasTrace_2778_ = lean_ctor_get_uint8(v_options_2772_, sizeof(void*)*1);
v___x_2779_ = lean_array_push(v___x_2769_, v_a_2767_);
v___x_2780_ = l_Array_append___redArg(v___x_2779_, v_a_2773_);
lean_dec(v_a_2773_);
if (v_hasTrace_2778_ == 0)
{
lean_object* v___x_2782_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2780_);
v___x_2782_ = v___x_2775_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2784_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_2785_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3, &l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3_once, _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3);
v___x_2786_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2777_, v_options_2772_, v___x_2785_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2788_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2780_);
v___x_2788_ = v___x_2775_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2780_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_del_object(v___x_2775_);
v___x_2790_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5, &l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5_once, _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5);
lean_inc_ref(v___x_2780_);
v___x_2791_ = lean_array_to_list(v___x_2780_);
v___x_2792_ = lean_box(0);
v___x_2793_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(v___x_2791_, v___x_2792_);
v___x_2794_ = l_Lean_MessageData_ofList(v___x_2793_);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2790_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v___x_2784_, v___x_2795_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2803_ == 0)
{
lean_object* v_unused_2804_; 
v_unused_2804_ = lean_ctor_get(v___x_2796_, 0);
lean_dec(v_unused_2804_);
v___x_2798_ = v___x_2796_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_dec(v___x_2796_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2780_);
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2780_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec_ref(v___x_2780_);
v_a_2805_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2796_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2796_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec_ref(v___x_2769_);
lean_dec(v_a_2767_);
v_a_2814_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2771_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2771_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_a_2765_);
lean_dec(v_declName_2753_);
v_a_2822_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2766_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2766_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_declName_2753_);
v_a_2830_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2764_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2764_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed(lean_object* v_declName_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(v_declName_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(lean_object* v_cls_2847_, lean_object* v_msg_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v_cls_2847_, v_msg_2848_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___boxed(lean_object* v_cls_2857_, lean_object* v_msg_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(v_cls_2857_, v_msg_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(lean_object* v_declName_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; lean_object* v_env_2871_; uint8_t v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2870_ = lean_st_ref_get(v___y_2868_);
v_env_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc_ref(v_env_2871_);
lean_dec(v___x_2870_);
v___x_2872_ = l_Lean_isInductiveCore(v_env_2871_, v_declName_2867_);
v___x_2873_ = lean_box(v___x_2872_);
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v_declName_2875_, v___y_2876_);
lean_dec(v___y_2876_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(lean_object* v_declName_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v_declName_2879_, v___y_2881_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___boxed(lean_object* v_declName_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(v_declName_2884_, v___y_2885_, v___y_2886_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(uint8_t v_____do__lift_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
if (v_____do__lift_2889_ == 0)
{
uint8_t v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2893_ = 1;
v___x_2894_ = lean_box(v___x_2893_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
else
{
uint8_t v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = 0;
v___x_2897_ = lean_box(v___x_2896_);
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
return v___x_2898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
uint8_t v_____do__lift_2462__boxed_2903_; lean_object* v_res_2904_; 
v_____do__lift_2462__boxed_2903_ = lean_unbox(v_____do__lift_2899_);
v_res_2904_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v_____do__lift_2462__boxed_2903_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(lean_object* v_as_2905_, size_t v_i_2906_, size_t v_stop_2907_, lean_object* v_b_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
uint8_t v___x_2912_; 
v___x_2912_ = lean_usize_dec_eq(v_i_2906_, v_stop_2907_);
if (v___x_2912_ == 0)
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_array_uget_borrowed(v_as_2905_, v_i_2906_);
lean_inc(v___x_2913_);
v___x_2914_ = l_Lean_Elab_Command_elabCommand(v___x_2913_, v___y_2909_, v___y_2910_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; size_t v___x_2916_; size_t v___x_2917_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref(v___x_2914_);
v___x_2916_ = ((size_t)1ULL);
v___x_2917_ = lean_usize_add(v_i_2906_, v___x_2916_);
v_i_2906_ = v___x_2917_;
v_b_2908_ = v_a_2915_;
goto _start;
}
else
{
return v___x_2914_;
}
}
else
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v_b_2908_);
return v___x_2919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1___boxed(lean_object* v_as_2920_, lean_object* v_i_2921_, lean_object* v_stop_2922_, lean_object* v_b_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
size_t v_i_boxed_2927_; size_t v_stop_boxed_2928_; lean_object* v_res_2929_; 
v_i_boxed_2927_ = lean_unbox_usize(v_i_2921_);
lean_dec(v_i_2921_);
v_stop_boxed_2928_ = lean_unbox_usize(v_stop_2922_);
lean_dec(v_stop_2922_);
v_res_2929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_as_2920_, v_i_boxed_2927_, v_stop_boxed_2928_, v_b_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec_ref(v_as_2920_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(lean_object* v___x_2930_, lean_object* v___x_2931_, lean_object* v___x_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_2930_, v___y_2933_, v___y_2934_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2956_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2956_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2956_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2941_ = lean_array_get_size(v_a_2937_);
v___x_2942_ = lean_nat_dec_lt(v___x_2931_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2944_; 
lean_dec(v_a_2937_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2932_);
v___x_2944_ = v___x_2939_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2932_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
else
{
uint8_t v___x_2946_; 
v___x_2946_ = lean_nat_dec_le(v___x_2941_, v___x_2941_);
if (v___x_2946_ == 0)
{
if (v___x_2942_ == 0)
{
lean_object* v___x_2948_; 
lean_dec(v_a_2937_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2932_);
v___x_2948_ = v___x_2939_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2932_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
else
{
size_t v___x_2950_; size_t v___x_2951_; lean_object* v___x_2952_; 
lean_del_object(v___x_2939_);
v___x_2950_ = ((size_t)0ULL);
v___x_2951_ = lean_usize_of_nat(v___x_2941_);
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_a_2937_, v___x_2950_, v___x_2951_, v___x_2932_, v___y_2933_, v___y_2934_);
lean_dec(v_a_2937_);
return v___x_2952_;
}
}
else
{
size_t v___x_2953_; size_t v___x_2954_; lean_object* v___x_2955_; 
lean_del_object(v___x_2939_);
v___x_2953_ = ((size_t)0ULL);
v___x_2954_ = lean_usize_of_nat(v___x_2941_);
v___x_2955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_a_2937_, v___x_2953_, v___x_2954_, v___x_2932_, v___y_2933_, v___y_2934_);
lean_dec(v_a_2937_);
return v___x_2955_;
}
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
v_a_2957_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2936_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2936_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed(lean_object* v___x_2965_, lean_object* v___x_2966_, lean_object* v___x_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(v___x_2965_, v___x_2966_, v___x_2967_, v___y_2968_, v___y_2969_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___x_2966_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(lean_object* v_as_2972_, size_t v_sz_2973_, size_t v_i_2974_, lean_object* v_b_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
uint8_t v___x_2979_; 
v___x_2979_ = lean_usize_dec_lt(v_i_2974_, v_sz_2973_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_b_2975_);
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v_a_2983_; lean_object* v___x_2984_; lean_object* v___f_2985_; lean_object* v___x_2986_; 
v___x_2981_ = lean_unsigned_to_nat(0u);
v___x_2982_ = lean_box(0);
v_a_2983_ = lean_array_uget_borrowed(v_as_2972_, v_i_2974_);
lean_inc_n(v_a_2983_, 2);
v___x_2984_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed), 8, 1);
lean_closure_set(v___x_2984_, 0, v_a_2983_);
v___f_2985_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2985_, 0, v___x_2984_);
lean_closure_set(v___f_2985_, 1, v___x_2981_);
lean_closure_set(v___f_2985_, 2, v___x_2982_);
v___x_2986_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_2983_, v___f_2985_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2986_) == 0)
{
size_t v___x_2987_; size_t v___x_2988_; 
lean_dec_ref(v___x_2986_);
v___x_2987_ = ((size_t)1ULL);
v___x_2988_ = lean_usize_add(v_i_2974_, v___x_2987_);
v_i_2974_ = v___x_2988_;
v_b_2975_ = v___x_2982_;
goto _start;
}
else
{
return v___x_2986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___boxed(lean_object* v_as_2990_, lean_object* v_sz_2991_, lean_object* v_i_2992_, lean_object* v_b_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
size_t v_sz_boxed_2997_; size_t v_i_boxed_2998_; lean_object* v_res_2999_; 
v_sz_boxed_2997_ = lean_unbox_usize(v_sz_2991_);
lean_dec(v_sz_2991_);
v_i_boxed_2998_ = lean_unbox_usize(v_i_2992_);
lean_dec(v_i_2992_);
v_res_2999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(v_as_2990_, v_sz_boxed_2997_, v_i_boxed_2998_, v_b_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v_as_2990_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(lean_object* v_as_3000_, size_t v_i_3001_, size_t v_stop_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
uint8_t v___x_3006_; 
v___x_3006_ = lean_usize_dec_eq(v_i_3001_, v_stop_3002_);
if (v___x_3006_ == 0)
{
uint8_t v___x_3007_; uint8_t v_a_3009_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3007_ = 1;
v___x_3015_ = lean_array_uget_borrowed(v_as_3000_, v_i_3001_);
lean_inc(v___x_3015_);
v___x_3016_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v___x_3015_, v___y_3004_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3026_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3019_ = v___x_3016_;
v_isShared_3020_ = v_isSharedCheck_3026_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3026_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
uint8_t v___x_3021_; 
v___x_3021_ = lean_unbox(v_a_3017_);
lean_dec(v_a_3017_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3022_ = lean_box(v___x_3007_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v___x_3022_);
v___x_3024_ = v___x_3019_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
else
{
lean_del_object(v___x_3019_);
v_a_3009_ = v___x_3006_;
goto v___jp_3008_;
}
}
}
else
{
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3027_; uint8_t v___x_3028_; 
v_a_3027_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3027_);
lean_dec_ref(v___x_3016_);
v___x_3028_ = lean_unbox(v_a_3027_);
lean_dec(v_a_3027_);
v_a_3009_ = v___x_3028_;
goto v___jp_3008_;
}
else
{
return v___x_3016_;
}
}
v___jp_3008_:
{
if (v_a_3009_ == 0)
{
size_t v___x_3010_; size_t v___x_3011_; 
v___x_3010_ = ((size_t)1ULL);
v___x_3011_ = lean_usize_add(v_i_3001_, v___x_3010_);
v_i_3001_ = v___x_3011_;
goto _start;
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_box(v___x_3007_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
}
}
else
{
uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3029_ = 0;
v___x_3030_ = lean_box(v___x_3029_);
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
return v___x_3031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3___boxed(lean_object* v_as_3032_, lean_object* v_i_3033_, lean_object* v_stop_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
size_t v_i_boxed_3038_; size_t v_stop_boxed_3039_; lean_object* v_res_3040_; 
v_i_boxed_3038_ = lean_unbox_usize(v_i_3033_);
lean_dec(v_i_3033_);
v_stop_boxed_3039_ = lean_unbox_usize(v_stop_3034_);
lean_dec(v_stop_3034_);
v_res_3040_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(v_as_3032_, v_i_boxed_3038_, v_stop_boxed_3039_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v_as_3032_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(lean_object* v_declNames_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v___y_3069_; lean_object* v___x_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; 
v___x_3072_ = lean_unsigned_to_nat(0u);
v___x_3073_ = lean_array_get_size(v_declNames_3041_);
v___x_3074_ = lean_nat_dec_lt(v___x_3072_, v___x_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v___x_3074_, v_a_3042_, v_a_3043_);
v___y_3069_ = v___x_3075_;
goto v___jp_3068_;
}
else
{
if (v___x_3074_ == 0)
{
goto v___jp_3045_;
}
else
{
size_t v___x_3076_; size_t v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = ((size_t)0ULL);
v___x_3077_ = lean_usize_of_nat(v___x_3073_);
v___x_3078_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(v_declNames_3041_, v___x_3076_, v___x_3077_, v_a_3042_, v_a_3043_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; uint8_t v___x_3080_; lean_object* v___x_3081_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3079_);
lean_dec_ref(v___x_3078_);
v___x_3080_ = lean_unbox(v_a_3079_);
lean_dec(v_a_3079_);
v___x_3081_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v___x_3080_, v_a_3042_, v_a_3043_);
v___y_3069_ = v___x_3081_;
goto v___jp_3068_;
}
else
{
v___y_3069_ = v___x_3078_;
goto v___jp_3068_;
}
}
}
v___jp_3045_:
{
lean_object* v___x_3046_; size_t v_sz_3047_; size_t v___x_3048_; lean_object* v___x_3049_; 
v___x_3046_ = lean_box(0);
v_sz_3047_ = lean_array_size(v_declNames_3041_);
v___x_3048_ = ((size_t)0ULL);
v___x_3049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(v_declNames_3041_, v_sz_3047_, v___x_3048_, v___x_3046_, v_a_3042_, v_a_3043_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3058_; 
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3058_ == 0)
{
lean_object* v_unused_3059_; 
v_unused_3059_ = lean_ctor_get(v___x_3049_, 0);
lean_dec(v_unused_3059_);
v___x_3051_ = v___x_3049_;
v_isShared_3052_ = v_isSharedCheck_3058_;
goto v_resetjp_3050_;
}
else
{
lean_dec(v___x_3049_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3058_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
uint8_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3053_ = 1;
v___x_3054_ = lean_box(v___x_3053_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3054_);
v___x_3056_ = v___x_3051_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
v_a_3060_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3049_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3049_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
v___jp_3068_:
{
if (lean_obj_tag(v___y_3069_) == 0)
{
lean_object* v_a_3070_; uint8_t v___x_3071_; 
v_a_3070_ = lean_ctor_get(v___y_3069_, 0);
v___x_3071_ = lean_unbox(v_a_3070_);
if (v___x_3071_ == 0)
{
return v___y_3069_;
}
else
{
lean_dec_ref(v___y_3069_);
goto v___jp_3045_;
}
}
else
{
return v___y_3069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed(lean_object* v_declNames_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(v_declNames_3082_, v_a_3083_, v_a_3084_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_declNames_3082_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
v___x_3155_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_));
v___x_3156_ = l_Lean_Elab_registerDerivingHandler(v___x_3154_, v___x_3155_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v___x_3157_; uint8_t v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_dec_ref(v___x_3156_);
v___x_3157_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_3158_ = 0;
v___x_3159_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_));
v___x_3160_ = l_Lean_registerTraceClass(v___x_3157_, v___x_3158_, v___x_3159_);
return v___x_3160_;
}
else
{
return v___x_3156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2____boxed(lean_object* v_a_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
return v_res_3162_;
}
}
lean_object* runtime_initialize_Lean_Meta_Inductive(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Repr(uint8_t builtin) {
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
res = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_Repr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Inductive(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Repr(uint8_t builtin) {
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
res = runtime_initialize_Lean_Elab_Deriving_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_Repr(builtin);
}
#ifdef __cplusplus
}
#endif
