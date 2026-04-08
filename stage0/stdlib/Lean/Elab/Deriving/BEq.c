// Lean compiler output
// Module: Lean.Elab.Deriving.BEq
// Imports: public import Lean.Data.Options import Lean.Elab.Deriving.Basic import Lean.Elab.Deriving.Util import Lean.Meta.Constructions.CtorIdx import Lean.Meta.Constructions.CasesOnSameCtor import Lean.Meta.SameCtorUtils import Init.Data.Array.OfFn
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_occursOrInType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* l_mkCtorIdxName(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnSameCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deriving"};
static const lean_object* l_Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "linear_construction_threshold"};
static const lean_object* l_Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 127, 229, 132, 157, 42, 70, 134)}};
static const lean_ctor_object l_Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(155, 188, 150, 126, 202, 210, 87, 56)}};
static const lean_ctor_object l_Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(2, 35, 48, 234, 208, 30, 169, 118)}};
static const lean_object* l_Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 350, .m_capacity = 350, .m_length = 349, .m_data = "If the inductive data type has this many or more constructors, use a different implementation for implementing `BEq` that avoids the quadratic code size produced by the default implementation.\n\nThe alternative construction compiles to less efficient code in some cases, so by default it is only used for inductive types with 10 or more constructors."};
static const lean_object* l_Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l_Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 26, 2, 19, 145, 121, 166, 213)}};
static const lean_ctor_object l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(83, 133, 133, 91, 54, 122, 56, 16)}};
static const lean_ctor_object l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(34, 240, 175, 247, 46, 32, 117, 152)}};
static const lean_ctor_object l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_5),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 170, 61, 15, 0, 197, 154, 83)}};
static const lean_object* l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_deriving_beq_linear__construction__threshold;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 214, 196, 140, 104, 187, 164, 111)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__8_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_&&_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(6, 195, 203, 117, 177, 125, 57, 22)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_==_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(25, 251, 60, 160, 118, 54, 158, 27)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=="};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "&&"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDepIfThenElse"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(191, 94, 17, 11, 145, 108, 236, 173)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__13_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__20_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__24_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(197, 49, 98, 208, 150, 151, 163, 74)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimTarget"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30_value),LEAN_SCALAR_PTR_LITERAL(136, 63, 46, 91, 99, 29, 205, 171)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__34_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__34_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__37_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__37_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 26, 2, 19, 145, 121, 166, 213)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__47 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__47_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__48 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__48_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__48_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__49 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__49_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__49_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__51 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__51_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__51_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_of_beq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53_value),LEAN_SCALAR_PTR_LITERAL(222, 43, 1, 254, 31, 20, 2, 112)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LawfulBEq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__56 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__56_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__56_value),LEAN_SCALAR_PTR_LITERAL(198, 131, 20, 143, 70, 69, 65, 69)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53_value),LEAN_SCALAR_PTR_LITERAL(55, 38, 224, 243, 7, 50, 169, 202)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__58 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__58_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__64 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__64_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__64_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inaccessible"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__66 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__66_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__66_value),LEAN_SCALAR_PTR_LITERAL(243, 90, 7, 119, 108, 205, 19, 233)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__68 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__68_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__6_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__7_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Elab.Deriving.BEq"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Elab.Deriving.BEq.0.Lean.Elab.Deriving.BEq.mkMatchNew"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: header.targetNames.size == 2\n\n  "};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "match_on_same_ctor"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 38, 237, 47, 106, 10, 11, 248)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__6_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decEq"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8_value),LEAN_SCALAR_PTR_LITERAL(173, 33, 189, 14, 17, 44, 93, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16_value),LEAN_SCALAR_PTR_LITERAL(125, 82, 240, 34, 69, 121, 64, 234)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value),LEAN_SCALAR_PTR_LITERAL(113, 70, 3, 12, 31, 103, 230, 247)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__12_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__16_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "set_option"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2_value),LEAN_SCALAR_PTR_LITERAL(216, 223, 149, 245, 150, 86, 134, 198)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "match.ignoreUnusedAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ignoreUnusedAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 5, 219, 45, 43, 52, 169, 192)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__6_value),LEAN_SCALAR_PTR_LITERAL(49, 254, 67, 85, 227, 127, 91, 187)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 204, 183, 225, 123, 221, 75, 96)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__8_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "x.ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(2, 247, 218, 116, 51, 159, 161, 152)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "y.ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(85, 37, 232, 186, 208, 254, 208, 112)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "method_specs"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(101, 159, 225, 215, 58, 146, 25, 204)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(254, 165, 225, 156, 115, 202, 230, 35)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(71, 221, 4, 81, 40, 1, 30, 26)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 242, 38, 149, 146, 119, 211, 138)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(120, 78, 208, 242, 44, 150, 100, 230)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 129, 112, 189, 241, 241, 163, 103)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(222, 208, 129, 142, 173, 19, 33, 85)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 135, 164, 219, 193, 11, 15, 193)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 118, 133, 101, 222, 86, 142, 163)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(47, 129, 53, 81, 247, 98, 179, 247)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 213, 169, 55, 145, 123, 160, 112)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(71, 28, 210, 8, 101, 35, 72, 179)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 53, 125, 167, 22, 113, 17, 93)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)(((size_t)(993467269) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(40, 184, 182, 130, 80, 10, 154, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 174, 45, 45, 68, 195, 231, 187)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 45, 241, 81, 166, 228, 249, 231)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(98, 175, 82, 143, 146, 81, 47, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
lean_inc(v_defValue_5_);
v___x_8_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_8_, 0, v_defValue_5_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_9_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_9_, 0, v_name_1_);
lean_ctor_set(v___x_9_, 1, v_ref_3_);
lean_ctor_set(v___x_9_, 2, v___x_8_);
lean_ctor_set(v___x_9_, 3, v_descr_6_);
lean_ctor_set(v___x_9_, 4, v_deprecation_x3f_7_);
v___x_10_ = lean_register_option(v_name_1_, v___x_9_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_18_; 
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_18_ == 0)
{
lean_object* v_unused_19_; 
v_unused_19_ = lean_ctor_get(v___x_10_, 0);
lean_dec(v_unused_19_);
v___x_12_ = v___x_10_;
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
else
{
lean_dec(v___x_10_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_16_; 
lean_inc(v_defValue_5_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v_name_1_);
lean_ctor_set(v___x_14_, 1, v_defValue_5_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_14_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
else
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
lean_dec(v_name_1_);
v_a_20_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_27_ == 0)
{
v___x_22_ = v___x_10_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_10_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_28_, lean_object* v_decl_29_, lean_object* v_ref_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Option_register___at___00Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(v_name_28_, v_decl_29_, v_ref_30_);
lean_dec_ref(v_decl_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((lean_object*)(l_Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l_Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l_Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_61_ = l_Lean_Option_register___at___00Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(lean_object* v_indVal_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = l_Lean_Elab_Deriving_mkHeader(v___x_74_, v___x_75_, v_indVal_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___boxed(lean_object* v_indVal_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(v_indVal_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_ref_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_ref_93_ = lean_ctor_get(v___y_90_, 5);
v___x_94_ = 0;
v___x_95_ = l_Lean_SourceInfo_fromRef(v_ref_93_, v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0___boxed(lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(lean_object* v_upperBound_114_, lean_object* v_a_115_, lean_object* v_b_116_, lean_object* v___y_117_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_nat_dec_lt(v_a_115_, v_upperBound_114_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_dec(v_a_115_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v_b_116_);
return v___x_120_;
}
else
{
lean_object* v_ref_121_; uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_ref_121_ = lean_ctor_get(v___y_117_, 5);
v___x_122_ = 0;
v___x_123_ = l_Lean_SourceInfo_fromRef(v_ref_121_, v___x_122_);
v___x_124_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_125_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
lean_inc(v___x_123_);
v___x_126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_123_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = l_Lean_Syntax_node1(v___x_123_, v___x_124_, v___x_126_);
v___x_128_ = lean_array_push(v_b_116_, v___x_127_);
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_add(v_a_115_, v___x_129_);
lean_dec(v_a_115_);
v_a_115_ = v___x_130_;
v_b_116_ = v___x_128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___boxed(lean_object* v_upperBound_132_, lean_object* v_a_133_, lean_object* v_b_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_upperBound_132_, v_a_133_, v_b_134_, v___y_135_);
lean_dec_ref(v___y_135_);
lean_dec(v_upperBound_132_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(size_t v_sz_138_, size_t v_i_139_, lean_object* v_bs_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = lean_usize_dec_lt(v_i_139_, v_sz_138_);
if (v___x_141_ == 0)
{
return v_bs_140_;
}
else
{
lean_object* v_v_142_; lean_object* v___x_143_; lean_object* v_bs_x27_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; 
v_v_142_ = lean_array_uget(v_bs_140_, v_i_139_);
v___x_143_ = lean_unsigned_to_nat(0u);
v_bs_x27_144_ = lean_array_uset(v_bs_140_, v_i_139_, v___x_143_);
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_add(v_i_139_, v___x_145_);
v___x_147_ = lean_array_uset(v_bs_x27_144_, v_i_139_, v_v_142_);
v_i_139_ = v___x_146_;
v_bs_140_ = v___x_147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0___boxed(lean_object* v_sz_149_, lean_object* v_i_150_, lean_object* v_bs_151_){
_start:
{
size_t v_sz_boxed_152_; size_t v_i_boxed_153_; lean_object* v_res_154_; 
v_sz_boxed_152_ = lean_unbox_usize(v_sz_149_);
lean_dec(v_sz_149_);
v_i_boxed_153_ = lean_unbox_usize(v_i_150_);
lean_dec(v_i_150_);
v_res_154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_boxed_152_, v_i_boxed_153_, v_bs_151_);
return v_res_154_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1));
v___x_159_ = l_String_toRawSubstring_x27(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13(void){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Array_mkArray0(lean_box(0));
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__14));
v___x_185_ = l_Lean_mkAtom(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(lean_object* v_indVal_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_numIndices_195_; lean_object* v___x_196_; lean_object* v_patterns_197_; lean_object* v___x_198_; 
v_numIndices_195_ = lean_ctor_get(v_indVal_187_, 2);
v___x_196_ = lean_unsigned_to_nat(0u);
v_patterns_197_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
v___x_198_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_numIndices_195_, v___x_196_, v_patterns_197_, v_a_192_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v_ref_200_; lean_object* v_quotContext_201_; lean_object* v_currMacroScope_202_; lean_object* v___x_203_; lean_object* v_a_204_; lean_object* v___x_205_; lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_242_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref(v___x_198_);
v_ref_200_ = lean_ctor_get(v_a_192_, 5);
v_quotContext_201_ = lean_ctor_get(v_a_192_, 10);
v_currMacroScope_202_ = lean_ctor_get(v_a_192_, 11);
v___x_203_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
v_a_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_a_204_);
lean_dec_ref(v___x_203_);
v___x_205_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_242_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_242_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_242_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; size_t v_sz_228_; size_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_210_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_211_ = 0;
v___x_212_ = l_Lean_SourceInfo_fromRef(v_ref_200_, v___x_211_);
v___x_213_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
lean_inc(v___x_212_);
v___x_214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_216_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_217_ = l_Lean_Syntax_node1(v___x_212_, v___x_216_, v___x_214_);
lean_inc(v___x_217_);
v___x_218_ = lean_array_push(v_a_199_, v___x_217_);
v___x_219_ = lean_array_push(v___x_218_, v___x_217_);
lean_inc(v_currMacroScope_202_);
lean_inc(v_quotContext_201_);
v___x_220_ = l_Lean_addMacroScope(v_quotContext_201_, v___x_215_, v_currMacroScope_202_);
v___x_221_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7));
v___x_222_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_222_, 0, v_a_204_);
lean_ctor_set(v___x_222_, 1, v___x_210_);
lean_ctor_set(v___x_222_, 2, v___x_220_);
lean_ctor_set(v___x_222_, 3, v___x_221_);
v___x_223_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_224_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
lean_inc_n(v_a_206_, 4);
v___x_225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_225_, 0, v_a_206_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_227_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v_sz_228_ = lean_array_size(v___x_219_);
v___x_229_ = ((size_t)0ULL);
v___x_230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_228_, v___x_229_, v___x_219_);
v___x_231_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_232_ = l_Lean_mkSepArray(v___x_230_, v___x_231_);
lean_dec_ref(v___x_230_);
v___x_233_ = l_Array_append___redArg(v___x_227_, v___x_232_);
lean_dec_ref(v___x_232_);
v___x_234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_234_, 0, v_a_206_);
lean_ctor_set(v___x_234_, 1, v___x_226_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
v___x_235_ = l_Lean_Syntax_node1(v_a_206_, v___x_226_, v___x_234_);
v___x_236_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_237_, 0, v_a_206_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = l_Lean_Syntax_node4(v_a_206_, v___x_223_, v___x_225_, v___x_235_, v___x_237_, v___x_222_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_238_);
v___x_240_ = v___x_208_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
v_a_243_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_198_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_198_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___boxed(lean_object* v_indVal_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(v_indVal_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_indVal_251_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1(lean_object* v_upperBound_260_, lean_object* v_inst_261_, lean_object* v_R_262_, lean_object* v_a_263_, lean_object* v_b_264_, lean_object* v_c_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_upperBound_260_, v_a_263_, v_b_264_, v___y_270_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___boxed(lean_object* v_upperBound_274_, lean_object* v_inst_275_, lean_object* v_R_276_, lean_object* v_a_277_, lean_object* v_b_278_, lean_object* v_c_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1(v_upperBound_274_, v_inst_275_, v_R_276_, v_a_277_, v_b_278_, v_c_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v_upperBound_274_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(lean_object* v_k_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v_b_291_, lean_object* v_c_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; 
lean_inc(v___y_296_);
lean_inc_ref(v___y_295_);
lean_inc(v___y_294_);
lean_inc_ref(v___y_293_);
lean_inc(v___y_290_);
lean_inc_ref(v___y_289_);
v___x_298_ = lean_apply_9(v_k_288_, v_b_291_, v_c_292_, v___y_289_, v___y_290_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, lean_box(0));
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed(lean_object* v_k_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v_b_302_, lean_object* v_c_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(v_k_299_, v___y_300_, v___y_301_, v_b_302_, v_c_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(lean_object* v_type_310_, lean_object* v_k_311_, uint8_t v_cleanupAnnotations_312_, uint8_t v_whnfType_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___f_321_; lean_object* v___x_322_; 
lean_inc(v___y_315_);
lean_inc_ref(v___y_314_);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_321_, 0, v_k_311_);
lean_closure_set(v___f_321_, 1, v___y_314_);
lean_closure_set(v___f_321_, 2, v___y_315_);
v___x_322_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_310_, v___f_321_, v_cleanupAnnotations_312_, v_whnfType_313_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_322_) == 0)
{
return v___x_322_;
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object* v_type_331_, lean_object* v_k_332_, lean_object* v_cleanupAnnotations_333_, lean_object* v_whnfType_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_342_; uint8_t v_whnfType_boxed_343_; lean_object* v_res_344_; 
v_cleanupAnnotations_boxed_342_ = lean_unbox(v_cleanupAnnotations_333_);
v_whnfType_boxed_343_ = lean_unbox(v_whnfType_334_);
v_res_344_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_331_, v_k_332_, v_cleanupAnnotations_boxed_342_, v_whnfType_boxed_343_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4(lean_object* v_00_u03b1_345_, lean_object* v_type_346_, lean_object* v_k_347_, uint8_t v_cleanupAnnotations_348_, uint8_t v_whnfType_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_346_, v_k_347_, v_cleanupAnnotations_348_, v_whnfType_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___boxed(lean_object* v_00_u03b1_358_, lean_object* v_type_359_, lean_object* v_k_360_, lean_object* v_cleanupAnnotations_361_, lean_object* v_whnfType_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_370_; uint8_t v_whnfType_boxed_371_; lean_object* v_res_372_; 
v_cleanupAnnotations_boxed_370_ = lean_unbox(v_cleanupAnnotations_361_);
v_whnfType_boxed_371_ = lean_unbox(v_whnfType_362_);
v_res_372_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4(v_00_u03b1_358_, v_type_359_, v_k_360_, v_cleanupAnnotations_boxed_370_, v_whnfType_boxed_371_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(lean_object* v___x_373_, lean_object* v_as_374_, size_t v_i_375_, size_t v_stop_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = lean_usize_dec_eq(v_i_375_, v_stop_376_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_array_uget_borrowed(v_as_374_, v_i_375_);
lean_inc(v___y_380_);
lean_inc_ref(v___y_379_);
lean_inc(v___y_378_);
lean_inc_ref(v___y_377_);
lean_inc(v___x_383_);
v___x_384_ = lean_infer_type(v___x_383_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_398_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_398_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_398_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_398_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = l_Lean_Expr_fvarId_x21(v___x_373_);
v___x_390_ = l_Lean_Expr_containsFVar(v_a_385_, v___x_389_);
lean_dec(v___x_389_);
lean_dec(v_a_385_);
if (v___x_390_ == 0)
{
size_t v___x_391_; size_t v___x_392_; 
lean_del_object(v___x_387_);
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_375_, v___x_391_);
v_i_375_ = v___x_392_;
goto _start;
}
else
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_box(v___x_390_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_394_);
v___x_396_ = v___x_387_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
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
v_a_399_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_384_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_384_);
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
else
{
uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = 0;
v___x_408_ = lean_box(v___x_407_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object* v___x_410_, lean_object* v_as_411_, lean_object* v_i_412_, lean_object* v_stop_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
size_t v_i_boxed_419_; size_t v_stop_boxed_420_; lean_object* v_res_421_; 
v_i_boxed_419_ = lean_unbox_usize(v_i_412_);
lean_dec(v_i_412_);
v_stop_boxed_420_ = lean_unbox_usize(v_stop_413_);
lean_dec(v_stop_413_);
v_res_421_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_410_, v_as_411_, v_i_boxed_419_, v_stop_boxed_420_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec_ref(v_as_411_);
lean_dec_ref(v___x_410_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_ref_429_; uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_ref_429_ = lean_ctor_get(v___y_426_, 5);
v___x_430_ = 0;
v___x_431_ = l_Lean_SourceInfo_fromRef(v_ref_429_, v___x_430_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0___boxed(lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_440_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15));
v___x_465_ = l_String_toRawSubstring_x27(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39));
v___x_520_ = l_String_toRawSubstring_x27(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53));
v___x_557_ = l_String_toRawSubstring_x27(v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(lean_object* v_upperBound_591_, lean_object* v_indVal_592_, lean_object* v___x_593_, lean_object* v_xs_594_, lean_object* v_a_595_, lean_object* v_auxFunName_596_, lean_object* v_a_597_, lean_object* v_b_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_a_607_; uint8_t v___x_611_; 
v___x_611_ = lean_nat_dec_lt(v_a_597_, v_upperBound_591_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_b_598_);
return v___x_612_;
}
else
{
lean_object* v_snd_613_; lean_object* v_snd_614_; lean_object* v_fst_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_967_; 
v_snd_613_ = lean_ctor_get(v_b_598_, 1);
lean_inc(v_snd_613_);
v_snd_614_ = lean_ctor_get(v_snd_613_, 1);
lean_inc(v_snd_614_);
v_fst_615_ = lean_ctor_get(v_b_598_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_b_598_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v_b_598_, 1);
lean_dec(v_unused_968_);
v___x_617_ = v_b_598_;
v_isShared_618_ = v_isSharedCheck_967_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_fst_615_);
lean_dec(v_b_598_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_967_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_fst_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_965_; 
v_fst_619_ = lean_ctor_get(v_snd_613_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v_snd_613_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v_snd_613_, 1);
lean_dec(v_unused_966_);
v___x_621_ = v_snd_613_;
v_isShared_622_ = v_isSharedCheck_965_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_fst_619_);
lean_dec(v_snd_613_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_965_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_fst_623_; lean_object* v_snd_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_964_; 
v_fst_623_ = lean_ctor_get(v_snd_614_, 0);
v_snd_624_ = lean_ctor_get(v_snd_614_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_snd_614_);
if (v_isSharedCheck_964_ == 0)
{
v___x_626_ = v_snd_614_;
v_isShared_627_ = v_isSharedCheck_964_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_snd_624_);
lean_inc(v_fst_623_);
lean_dec(v_snd_614_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_964_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_toConstantVal_628_; lean_object* v_numParams_629_; lean_object* v_lctx_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_toConstantVal_628_ = lean_ctor_get(v_indVal_592_, 0);
lean_inc_ref(v_toConstantVal_628_);
v_numParams_629_ = lean_ctor_get(v_indVal_592_, 1);
v_lctx_630_ = lean_ctor_get(v___y_601_, 2);
v___x_631_ = l_Lean_instInhabitedExpr;
v___x_632_ = lean_nat_add(v_numParams_629_, v___x_593_);
v___x_633_ = lean_nat_sub(v___x_632_, v_a_597_);
lean_dec(v___x_632_);
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_sub(v___x_633_, v___x_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_array_get_borrowed(v___x_631_, v_xs_594_, v___x_635_);
lean_inc(v___x_636_);
lean_inc_ref(v_lctx_630_);
v___x_637_ = l_Lean_Meta_occursOrInType(v_lctx_630_, v___x_636_, v_a_595_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1));
v___x_639_ = l_Lean_Core_mkFreshUserName(v___x_638_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref(v___x_639_);
v___x_641_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__3));
v___x_642_ = l_Lean_Core_mkFreshUserName(v___x_641_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref(v___x_642_);
lean_inc(v___y_604_);
lean_inc_ref(v___y_603_);
lean_inc(v___y_602_);
lean_inc_ref(v___y_601_);
lean_inc(v___x_636_);
v___x_644_ = lean_infer_type(v___x_636_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc_n(v_a_645_, 2);
lean_dec_ref(v___x_644_);
v___x_646_ = l_Lean_Meta_isProp(v_a_645_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref(v___x_646_);
v___x_648_ = lean_mk_syntax_ident(v_a_640_);
v___x_649_ = lean_mk_syntax_ident(v_a_643_);
lean_inc(v___x_648_);
v___x_650_ = lean_array_push(v_fst_615_, v___x_648_);
lean_inc(v___x_649_);
v___x_651_ = lean_array_push(v_fst_619_, v___x_649_);
v___x_652_ = lean_unbox(v_a_647_);
if (v___x_652_ == 0)
{
lean_object* v_name_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_881_; 
v_name_653_ = lean_ctor_get(v_toConstantVal_628_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_toConstantVal_628_);
if (v_isSharedCheck_881_ == 0)
{
lean_object* v_unused_882_; lean_object* v_unused_883_; 
v_unused_882_ = lean_ctor_get(v_toConstantVal_628_, 2);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_toConstantVal_628_, 1);
lean_dec(v_unused_883_);
v___x_655_ = v_toConstantVal_628_;
v_isShared_656_ = v_isSharedCheck_881_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_name_653_);
lean_dec(v_toConstantVal_628_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_881_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
uint8_t v___x_657_; uint8_t v_a_659_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v_lower_827_; lean_object* v_upper_828_; 
v___x_657_ = l_Lean_Expr_isAppOf(v_a_645_, v_name_653_);
lean_dec(v_name_653_);
lean_dec(v_a_645_);
if (v___x_657_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
lean_dec(v_a_647_);
v___x_836_ = lean_nat_add(v___x_635_, v___x_634_);
lean_dec(v___x_635_);
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = lean_array_get_size(v_xs_594_);
v___x_839_ = lean_nat_dec_le(v___x_836_, v___x_837_);
if (v___x_839_ == 0)
{
v_lower_827_ = v___x_836_;
v_upper_828_ = v___x_838_;
goto v___jp_826_;
}
else
{
lean_dec(v___x_836_);
v_lower_827_ = v___x_837_;
v_upper_828_ = v___x_838_;
goto v___jp_826_;
}
}
else
{
uint8_t v___x_840_; 
lean_del_object(v___x_655_);
lean_dec(v___x_635_);
lean_del_object(v___x_626_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
v___x_840_ = lean_unbox(v_snd_624_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec(v_a_647_);
v___x_841_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc_n(v_a_842_, 4);
lean_dec_ref(v___x_841_);
v___x_843_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_844_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_596_);
v___x_845_ = lean_mk_syntax_ident(v_auxFunName_596_);
v___x_846_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_847_ = l_Lean_Syntax_node2(v_a_842_, v___x_846_, v___x_648_, v___x_649_);
v___x_848_ = l_Lean_Syntax_node2(v_a_842_, v___x_844_, v___x_845_, v___x_847_);
v___x_849_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_850_, 0, v_a_842_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_Syntax_node3(v_a_842_, v___x_843_, v___x_848_, v___x_850_, v_fst_623_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_ctor_set(v___x_852_, 1, v_snd_624_);
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_651_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_650_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v_a_607_ = v___x_854_;
goto v___jp_606_;
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_624_);
lean_dec(v_fst_623_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_855_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_841_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_841_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v___x_863_; 
lean_dec(v_snd_624_);
lean_dec(v_fst_623_);
v___x_863_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc_n(v_a_864_, 2);
lean_dec_ref(v___x_863_);
v___x_865_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_596_);
v___x_866_ = lean_mk_syntax_ident(v_auxFunName_596_);
v___x_867_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_868_ = l_Lean_Syntax_node2(v_a_864_, v___x_867_, v___x_648_, v___x_649_);
v___x_869_ = l_Lean_Syntax_node2(v_a_864_, v___x_865_, v___x_866_, v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v_a_647_);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_651_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_650_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v_a_607_ = v___x_872_;
goto v___jp_606_;
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_a_647_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_873_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_863_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_863_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
v___jp_658_:
{
if (v_a_659_ == 0)
{
uint8_t v___x_660_; 
lean_del_object(v___x_655_);
v___x_660_ = lean_unbox(v_snd_624_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
v___x_661_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc_n(v_a_662_, 4);
lean_dec_ref(v___x_661_);
v___x_663_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_664_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_665_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_666_, 0, v_a_662_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_Syntax_node3(v_a_662_, v___x_664_, v___x_648_, v___x_666_, v___x_649_);
v___x_668_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_669_, 0, v_a_662_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = l_Lean_Syntax_node3(v_a_662_, v___x_663_, v___x_667_, v___x_669_, v_fst_623_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_670_);
v___x_672_ = v___x_626_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_snd_624_);
v___x_672_ = v_reuseFailAlloc_679_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_674_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_672_);
lean_ctor_set(v___x_621_, 0, v___x_651_);
v___x_674_ = v___x_621_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_674_);
lean_ctor_set(v___x_617_, 0, v___x_650_);
v___x_676_ = v___x_617_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v_a_607_ = v___x_676_;
goto v___jp_606_;
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_del_object(v___x_626_);
lean_dec(v_snd_624_);
lean_dec(v_fst_623_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_680_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_661_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_661_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v___x_688_; 
lean_dec(v_snd_624_);
lean_dec(v_fst_623_);
v___x_688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc_n(v_a_689_, 2);
lean_dec_ref(v___x_688_);
v___x_690_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_691_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_692_, 0, v_a_689_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = l_Lean_Syntax_node3(v_a_689_, v___x_690_, v___x_648_, v___x_692_, v___x_649_);
v___x_694_ = lean_box(v_a_659_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_694_);
lean_ctor_set(v___x_626_, 0, v___x_693_);
v___x_696_ = v___x_626_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_703_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_696_);
lean_ctor_set(v___x_621_, 0, v___x_651_);
v___x_698_ = v___x_621_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_696_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_698_);
lean_ctor_set(v___x_617_, 0, v___x_650_);
v___x_700_ = v___x_617_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
v_a_607_ = v___x_700_;
goto v___jp_606_;
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_del_object(v___x_626_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_704_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_688_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_688_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
else
{
lean_object* v___x_712_; 
lean_dec(v_snd_624_);
v___x_712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v_quotContext_714_; lean_object* v_currMacroScope_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc_n(v_a_713_, 11);
lean_dec_ref(v___x_712_);
v_quotContext_714_ = lean_ctor_get(v___y_603_, 10);
v_currMacroScope_715_ = lean_ctor_get(v___y_603_, 11);
v___x_716_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11));
v___x_717_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12));
v___x_718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_718_, 0, v_a_713_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14));
v___x_720_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_721_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
lean_inc(v_currMacroScope_715_);
lean_inc(v_quotContext_714_);
v___x_722_ = l_Lean_addMacroScope(v_quotContext_714_, v___x_721_, v_currMacroScope_715_);
v___x_723_ = lean_box(0);
v___x_724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_724_, 0, v_a_713_);
lean_ctor_set(v___x_724_, 1, v___x_720_);
lean_ctor_set(v___x_724_, 2, v___x_722_);
lean_ctor_set(v___x_724_, 3, v___x_723_);
lean_inc_ref(v___x_724_);
v___x_725_ = l_Lean_Syntax_node1(v_a_713_, v___x_719_, v___x_724_);
v___x_726_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_727_, 0, v_a_713_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_729_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_730_, 0, v_a_713_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = l_Lean_Syntax_node3(v_a_713_, v___x_728_, v___x_648_, v___x_730_, v___x_649_);
v___x_732_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19));
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v_a_713_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21));
v___x_735_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22));
v___x_736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_736_, 0, v_a_713_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25));
v___x_738_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27));
v___x_739_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28));
v___x_741_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29));
v___x_742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_742_, 0, v_a_713_);
lean_ctor_set(v___x_742_, 1, v___x_740_);
v___x_743_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31));
v___x_744_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 1);
lean_ctor_set(v___x_655_, 2, v___x_744_);
lean_ctor_set(v___x_655_, 1, v___x_739_);
lean_ctor_set(v___x_655_, 0, v_a_713_);
v___x_746_ = v___x_655_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_713_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v___x_744_);
v___x_746_ = v_reuseFailAlloc_799_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_747_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_748_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_749_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
lean_inc_n(v_a_713_, 20);
v___x_750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_750_, 0, v_a_713_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_752_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_753_ = lean_box(0);
lean_inc_n(v_currMacroScope_715_, 3);
lean_inc_n(v_quotContext_714_, 3);
v___x_754_ = l_Lean_addMacroScope(v_quotContext_714_, v___x_753_, v_currMacroScope_715_);
v___x_755_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50));
v___x_756_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_756_, 0, v_a_713_);
lean_ctor_set(v___x_756_, 1, v___x_752_);
lean_ctor_set(v___x_756_, 2, v___x_754_);
lean_ctor_set(v___x_756_, 3, v___x_755_);
v___x_757_ = l_Lean_Syntax_node1(v_a_713_, v___x_751_, v___x_756_);
v___x_758_ = l_Lean_Syntax_node2(v_a_713_, v___x_748_, v___x_750_, v___x_757_);
v___x_759_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_760_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54);
v___x_761_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55));
v___x_762_ = l_Lean_addMacroScope(v_quotContext_714_, v___x_761_, v_currMacroScope_715_);
v___x_763_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59));
v___x_764_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_764_, 0, v_a_713_);
lean_ctor_set(v___x_764_, 1, v___x_760_);
lean_ctor_set(v___x_764_, 2, v___x_762_);
lean_ctor_set(v___x_764_, 3, v___x_763_);
v___x_765_ = l_Lean_Syntax_node1(v_a_713_, v___x_739_, v___x_724_);
v___x_766_ = l_Lean_Syntax_node2(v_a_713_, v___x_759_, v___x_764_, v___x_765_);
v___x_767_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_768_, 0, v_a_713_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Lean_Syntax_node3(v_a_713_, v___x_747_, v___x_758_, v___x_766_, v___x_768_);
lean_inc_ref_n(v___x_746_, 3);
v___x_770_ = l_Lean_Syntax_node2(v_a_713_, v___x_743_, v___x_746_, v___x_769_);
v___x_771_ = l_Lean_Syntax_node1(v_a_713_, v___x_739_, v___x_770_);
v___x_772_ = l_Lean_Syntax_node4(v_a_713_, v___x_741_, v___x_742_, v___x_771_, v___x_746_, v___x_746_);
v___x_773_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61));
v___x_774_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62));
v___x_775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_775_, 0, v_a_713_);
lean_ctor_set(v___x_775_, 1, v___x_773_);
v___x_776_ = l_Lean_Syntax_node2(v_a_713_, v___x_774_, v___x_775_, v_fst_623_);
v___x_777_ = l_Lean_Syntax_node3(v_a_713_, v___x_739_, v___x_772_, v___x_746_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node1(v_a_713_, v___x_738_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node1(v_a_713_, v___x_737_, v___x_778_);
v___x_780_ = l_Lean_Syntax_node2(v_a_713_, v___x_734_, v___x_736_, v___x_779_);
v___x_781_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63));
v___x_782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_782_, 0, v_a_713_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_785_ = l_Lean_addMacroScope(v_quotContext_714_, v___x_784_, v_currMacroScope_715_);
v___x_786_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65));
v___x_787_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_787_, 0, v_a_713_);
lean_ctor_set(v___x_787_, 1, v___x_783_);
lean_ctor_set(v___x_787_, 2, v___x_785_);
lean_ctor_set(v___x_787_, 3, v___x_786_);
v___x_788_ = l_Lean_Syntax_node8(v_a_713_, v___x_716_, v___x_718_, v___x_725_, v___x_727_, v___x_731_, v___x_733_, v___x_780_, v___x_782_, v___x_787_);
v___x_789_ = lean_box(v___x_657_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_789_);
lean_ctor_set(v___x_626_, 0, v___x_788_);
v___x_791_ = v___x_626_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_789_);
v___x_791_ = v_reuseFailAlloc_798_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_791_);
lean_ctor_set(v___x_621_, 0, v___x_651_);
v___x_793_ = v___x_621_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_793_);
lean_ctor_set(v___x_617_, 0, v___x_650_);
v___x_795_ = v___x_617_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v_a_607_ = v___x_795_;
goto v___jp_606_;
}
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_del_object(v___x_655_);
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_del_object(v___x_626_);
lean_dec(v_fst_623_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_800_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_712_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_712_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
v___jp_808_:
{
uint8_t v___x_812_; 
v___x_812_ = lean_nat_dec_lt(v___y_809_, v___y_811_);
if (v___x_812_ == 0)
{
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
v_a_659_ = v___x_657_;
goto v___jp_658_;
}
else
{
size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; 
v___x_813_ = lean_usize_of_nat(v___y_809_);
lean_dec(v___y_809_);
v___x_814_ = lean_usize_of_nat(v___y_811_);
lean_dec(v___y_811_);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_636_, v___y_810_, v___x_813_, v___x_814_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec_ref(v___y_810_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; uint8_t v___x_817_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref(v___x_815_);
v___x_817_ = lean_unbox(v_a_816_);
lean_dec(v_a_816_);
v_a_659_ = v___x_817_;
goto v___jp_658_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_del_object(v___x_655_);
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_del_object(v___x_626_);
lean_dec(v_snd_624_);
lean_dec(v_fst_623_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_818_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_815_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_815_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
v___jp_826_:
{
lean_object* v___x_829_; lean_object* v_array_830_; lean_object* v_start_831_; lean_object* v_stop_832_; uint8_t v___x_833_; 
lean_inc_ref(v_xs_594_);
v___x_829_ = l_Array_toSubarray___redArg(v_xs_594_, v_lower_827_, v_upper_828_);
v_array_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc_ref(v_array_830_);
v_start_831_ = lean_ctor_get(v___x_829_, 1);
lean_inc(v_start_831_);
v_stop_832_ = lean_ctor_get(v___x_829_, 2);
lean_inc(v_stop_832_);
lean_dec_ref(v___x_829_);
v___x_833_ = lean_nat_dec_lt(v_start_831_, v_stop_832_);
if (v___x_833_ == 0)
{
lean_dec(v_stop_832_);
lean_dec(v_start_831_);
lean_dec_ref(v_array_830_);
v_a_659_ = v___x_657_;
goto v___jp_658_;
}
else
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_array_get_size(v_array_830_);
v___x_835_ = lean_nat_dec_le(v_stop_832_, v___x_834_);
if (v___x_835_ == 0)
{
lean_dec(v_stop_832_);
v___y_809_ = v_start_831_;
v___y_810_ = v_array_830_;
v___y_811_ = v___x_834_;
goto v___jp_808_;
}
else
{
v___y_809_ = v_start_831_;
v___y_810_ = v_array_830_;
v___y_811_ = v_stop_832_;
goto v___jp_808_;
}
}
}
}
}
else
{
lean_object* v___x_885_; 
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_a_647_);
lean_dec(v_a_645_);
lean_dec(v___x_635_);
lean_dec_ref(v_toConstantVal_628_);
if (v_isShared_627_ == 0)
{
v___x_885_ = v___x_626_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_fst_623_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_snd_624_);
v___x_885_ = v_reuseFailAlloc_892_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_885_);
lean_ctor_set(v___x_621_, 0, v___x_651_);
v___x_887_ = v___x_621_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_887_);
lean_ctor_set(v___x_617_, 0, v___x_650_);
v___x_889_ = v___x_617_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
v_a_607_ = v___x_889_;
goto v___jp_606_;
}
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v_a_645_);
lean_dec(v_a_643_);
lean_dec(v_a_640_);
lean_dec(v___x_635_);
lean_dec_ref(v_toConstantVal_628_);
lean_del_object(v___x_626_);
lean_dec(v_snd_624_);
lean_dec(v_fst_623_);
lean_del_object(v___x_621_);
lean_dec(v_fst_619_);
lean_del_object(v___x_617_);
lean_dec(v_fst_615_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_893_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_646_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_646_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_a_643_);
lean_dec(v_a_640_);
lean_dec(v___x_635_);
lean_dec_ref(v_toConstantVal_628_);
lean_del_object(v___x_626_);
lean_dec(v_snd_624_);
lean_dec(v_fst_623_);
lean_del_object(v___x_621_);
lean_dec(v_fst_619_);
lean_del_object(v___x_617_);
lean_dec(v_fst_615_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_901_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_644_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_644_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec(v_a_640_);
lean_dec(v___x_635_);
lean_dec_ref(v_toConstantVal_628_);
lean_del_object(v___x_626_);
lean_dec(v_snd_624_);
lean_dec(v_fst_623_);
lean_del_object(v___x_621_);
lean_dec(v_fst_619_);
lean_del_object(v___x_617_);
lean_dec(v_fst_615_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_909_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_642_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_642_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v___x_635_);
lean_dec_ref(v_toConstantVal_628_);
lean_del_object(v___x_626_);
lean_dec(v_snd_624_);
lean_dec(v_fst_623_);
lean_del_object(v___x_621_);
lean_dec(v_fst_619_);
lean_del_object(v___x_617_);
lean_dec(v_fst_615_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_917_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_639_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_639_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v___x_635_);
lean_dec_ref(v_toConstantVal_628_);
v___x_925_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1));
v___x_926_ = l_Lean_Core_mkFreshUserName(v___x_925_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_928_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v___x_928_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc_n(v_a_929_, 3);
lean_dec_ref(v___x_928_);
v___x_930_ = lean_mk_syntax_ident(v_a_927_);
lean_inc(v___x_930_);
v___x_931_ = lean_array_push(v_fst_615_, v___x_930_);
v___x_932_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67));
v___x_933_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__68));
v___x_934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_934_, 0, v_a_929_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_936_, 0, v_a_929_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l_Lean_Syntax_node3(v_a_929_, v___x_932_, v___x_934_, v___x_930_, v___x_936_);
v___x_938_ = lean_array_push(v_fst_619_, v___x_937_);
if (v_isShared_627_ == 0)
{
v___x_940_ = v___x_626_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fst_623_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_snd_624_);
v___x_940_ = v_reuseFailAlloc_947_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_940_);
lean_ctor_set(v___x_621_, 0, v___x_938_);
v___x_942_ = v___x_621_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_940_);
v___x_942_ = v_reuseFailAlloc_946_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_942_);
lean_ctor_set(v___x_617_, 0, v___x_931_);
v___x_944_ = v___x_617_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
v_a_607_ = v___x_944_;
goto v___jp_606_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_a_927_);
lean_del_object(v___x_626_);
lean_dec(v_snd_624_);
lean_dec(v_fst_623_);
lean_del_object(v___x_621_);
lean_dec(v_fst_619_);
lean_del_object(v___x_617_);
lean_dec(v_fst_615_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_948_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_928_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_928_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_del_object(v___x_626_);
lean_dec(v_snd_624_);
lean_dec(v_fst_623_);
lean_del_object(v___x_621_);
lean_dec(v_fst_619_);
lean_del_object(v___x_617_);
lean_dec(v_fst_615_);
lean_dec(v_a_597_);
lean_dec(v_auxFunName_596_);
lean_dec_ref(v_xs_594_);
lean_dec_ref(v_indVal_592_);
v_a_956_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_926_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_926_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
}
}
v___jp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_add(v_a_597_, v___x_608_);
lean_dec(v_a_597_);
v_a_597_ = v___x_609_;
v_b_598_ = v_a_607_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_969_, lean_object* v_indVal_970_, lean_object* v___x_971_, lean_object* v_xs_972_, lean_object* v_a_973_, lean_object* v_auxFunName_974_, lean_object* v_a_975_, lean_object* v_b_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_969_, v_indVal_970_, v___x_971_, v_xs_972_, v_a_973_, v_auxFunName_974_, v_a_975_, v_b_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec_ref(v_a_973_);
lean_dec(v___x_971_);
lean_dec(v_upperBound_969_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(lean_object* v_upperBound_985_, lean_object* v_a_986_, lean_object* v_b_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
uint8_t v___x_995_; 
v___x_995_ = lean_nat_dec_lt(v_a_986_, v_upperBound_985_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
lean_dec(v_a_986_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v_b_987_);
return v___x_996_;
}
else
{
lean_object* v___x_997_; 
v___x_997_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref(v___x_997_);
v___x_999_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v_fst_1001_; lean_object* v_snd_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1020_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v_fst_1001_ = lean_ctor_get(v_b_987_, 0);
v_snd_1002_ = lean_ctor_get(v_b_987_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_b_987_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1004_ = v_b_987_;
v_isShared_1005_ = v_isSharedCheck_1020_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_snd_1002_);
lean_inc(v_fst_1001_);
lean_dec(v_b_987_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1020_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1006_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
lean_inc(v_a_998_);
v___x_1007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_a_998_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_1009_ = l_Lean_Syntax_node1(v_a_998_, v___x_1008_, v___x_1007_);
v___x_1010_ = lean_array_push(v_fst_1001_, v___x_1009_);
lean_inc(v_a_1000_);
v___x_1011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_a_1000_);
lean_ctor_set(v___x_1011_, 1, v___x_1006_);
v___x_1012_ = l_Lean_Syntax_node1(v_a_1000_, v___x_1008_, v___x_1011_);
v___x_1013_ = lean_array_push(v_snd_1002_, v___x_1012_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v___x_1013_);
lean_ctor_set(v___x_1004_, 0, v___x_1010_);
v___x_1015_ = v___x_1004_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v_a_986_, v___x_1016_);
lean_dec(v_a_986_);
v_a_986_ = v___x_1017_;
v_b_987_ = v___x_1015_;
goto _start;
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v_a_998_);
lean_dec_ref(v_b_987_);
lean_dec(v_a_986_);
v_a_1021_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_999_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_999_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v_b_987_);
lean_dec(v_a_986_);
v_a_1029_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_997_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_997_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___boxed(lean_object* v_upperBound_1037_, lean_object* v_a_1038_, lean_object* v_b_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_upperBound_1037_, v_a_1038_, v_b_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v_upperBound_1037_);
return v_res_1047_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0));
v___x_1050_ = l_String_toRawSubstring_x27(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1(lean_object* v_indVal_1069_, lean_object* v___x_1070_, lean_object* v_alts_1071_, lean_object* v_numFields_1072_, lean_object* v_auxFunName_1073_, lean_object* v___f_1074_, lean_object* v_head_1075_, lean_object* v_xs_1076_, lean_object* v_type_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Core_betaReduce(v_type_1077_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v_numParams_1087_; lean_object* v_numIndices_1088_; lean_object* v___x_1089_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref(v___x_1085_);
v_numParams_1087_ = lean_ctor_get(v_indVal_1069_, 1);
lean_inc(v_numParams_1087_);
v_numIndices_1088_ = lean_ctor_get(v_indVal_1069_, 2);
lean_inc_ref(v_alts_1071_);
lean_inc(v___x_1070_);
v___x_1089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_numIndices_1088_, v___x_1070_, v_alts_1071_, v___y_1082_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v_ref_1091_; lean_object* v_quotContext_1092_; lean_object* v_currMacroScope_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref(v___x_1089_);
v_ref_1091_ = lean_ctor_get(v___y_1082_, 5);
v_quotContext_1092_ = lean_ctor_get(v___y_1082_, 10);
v_currMacroScope_1093_ = lean_ctor_get(v___y_1082_, 11);
v___x_1094_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1);
v___x_1095_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2));
v___x_1096_ = 0;
v___x_1097_ = l_Lean_SourceInfo_fromRef(v_ref_1091_, v___x_1096_);
lean_inc(v_currMacroScope_1093_);
lean_inc(v_quotContext_1092_);
v___x_1098_ = l_Lean_addMacroScope(v_quotContext_1092_, v___x_1095_, v_currMacroScope_1093_);
v___x_1099_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5));
v___x_1100_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1097_);
lean_ctor_set(v___x_1100_, 1, v___x_1094_);
lean_ctor_set(v___x_1100_, 2, v___x_1098_);
lean_ctor_set(v___x_1100_, 3, v___x_1099_);
v___x_1101_ = 1;
v___x_1102_ = lean_box(v___x_1101_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1100_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
lean_inc_ref(v_alts_1071_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_alts_1071_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_alts_1071_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
lean_inc(v___x_1070_);
v___x_1106_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_numFields_1072_, v_indVal_1069_, v_numFields_1072_, v_xs_1076_, v_a_1086_, v_auxFunName_1073_, v___x_1070_, v___x_1105_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v_a_1086_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v_snd_1108_; lean_object* v_snd_1109_; lean_object* v_fst_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1222_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref(v___x_1106_);
v_snd_1108_ = lean_ctor_get(v_a_1107_, 1);
lean_inc(v_snd_1108_);
v_snd_1109_ = lean_ctor_get(v_snd_1108_, 1);
lean_inc(v_snd_1109_);
v_fst_1110_ = lean_ctor_get(v_a_1107_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_a_1107_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_a_1107_, 1);
lean_dec(v_unused_1223_);
v___x_1112_ = v_a_1107_;
v_isShared_1113_ = v_isSharedCheck_1222_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_fst_1110_);
lean_dec(v_a_1107_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1222_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_fst_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1220_; 
v_fst_1114_ = lean_ctor_get(v_snd_1108_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_snd_1108_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_snd_1108_, 1);
lean_dec(v_unused_1221_);
v___x_1116_ = v_snd_1108_;
v_isShared_1117_ = v_isSharedCheck_1220_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_fst_1114_);
lean_dec(v_snd_1108_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1220_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_fst_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1218_; 
v_fst_1118_ = lean_ctor_get(v_snd_1109_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_snd_1109_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_snd_1109_, 1);
lean_dec(v_unused_1219_);
v___x_1120_ = v_snd_1109_;
v_isShared_1121_ = v_isSharedCheck_1218_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_fst_1118_);
lean_dec(v_snd_1109_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1218_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v_fst_1114_);
lean_ctor_set(v___x_1120_, 0, v_fst_1110_);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_fst_1110_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_fst_1114_);
v___x_1123_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_numParams_1087_, v___x_1070_, v___x_1123_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v_numParams_1087_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1126_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref(v___x_1124_);
lean_inc_ref(v___f_1074_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
v___x_1126_ = lean_apply_7(v___f_1074_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1128_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref(v___x_1126_);
lean_inc_ref(v___f_1074_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
v___x_1128_ = lean_apply_7(v___f_1074_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref(v___x_1128_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
v___x_1130_ = lean_apply_7(v___f_1074_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1184_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1184_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1184_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1183_; 
v_fst_1135_ = lean_ctor_get(v_a_1125_, 0);
v_snd_1136_ = lean_ctor_get(v_a_1125_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_a_1125_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1138_ = v_a_1125_;
v_isShared_1139_ = v_isSharedCheck_1183_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_snd_1136_);
lean_inc(v_fst_1135_);
lean_dec(v_a_1125_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1183_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1140_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_1141_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6));
lean_inc(v_a_1127_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set_tag(v___x_1138_, 2);
lean_ctor_set(v___x_1138_, 1, v___x_1141_);
lean_ctor_set(v___x_1138_, 0, v_a_1127_);
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1127_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = lean_mk_syntax_ident(v_head_1075_);
lean_inc(v_a_1129_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 2);
lean_ctor_set(v___x_1116_, 1, v___x_1141_);
lean_ctor_set(v___x_1116_, 0, v_a_1129_);
v___x_1146_ = v___x_1116_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1129_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1141_);
v___x_1146_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1147_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8));
lean_inc(v___x_1144_);
lean_inc_n(v_a_1127_, 2);
v___x_1148_ = l_Lean_Syntax_node2(v_a_1127_, v___x_1147_, v___x_1143_, v___x_1144_);
lean_inc_n(v_a_1129_, 2);
v___x_1149_ = l_Lean_Syntax_node2(v_a_1129_, v___x_1147_, v___x_1146_, v___x_1144_);
v___x_1150_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_1151_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_1152_ = l_Array_reverse___redArg(v_fst_1135_);
v___x_1153_ = l_Array_append___redArg(v___x_1151_, v___x_1152_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1154_, 0, v_a_1127_);
lean_ctor_set(v___x_1154_, 1, v___x_1150_);
lean_ctor_set(v___x_1154_, 2, v___x_1153_);
v___x_1155_ = l_Array_reverse___redArg(v_snd_1136_);
v___x_1156_ = l_Array_append___redArg(v___x_1151_, v___x_1155_);
lean_dec_ref(v___x_1155_);
v___x_1157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1157_, 0, v_a_1129_);
lean_ctor_set(v___x_1157_, 1, v___x_1150_);
lean_ctor_set(v___x_1157_, 2, v___x_1156_);
v___x_1158_ = l_Lean_Syntax_node2(v_a_1127_, v___x_1140_, v___x_1148_, v___x_1154_);
v___x_1159_ = lean_array_push(v_a_1090_, v___x_1158_);
v___x_1160_ = l_Lean_Syntax_node2(v_a_1129_, v___x_1140_, v___x_1149_, v___x_1157_);
v___x_1161_ = lean_array_push(v___x_1159_, v___x_1160_);
v___x_1162_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_1163_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
lean_inc(v_a_1131_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 2);
lean_ctor_set(v___x_1112_, 1, v___x_1163_);
lean_ctor_set(v___x_1112_, 0, v_a_1131_);
v___x_1165_ = v___x_1112_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1131_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
size_t v_sz_1166_; size_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v_sz_1166_ = lean_array_size(v___x_1161_);
v___x_1167_ = ((size_t)0ULL);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_1166_, v___x_1167_, v___x_1161_);
v___x_1169_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_1170_ = l_Lean_mkSepArray(v___x_1168_, v___x_1169_);
lean_dec_ref(v___x_1168_);
v___x_1171_ = l_Array_append___redArg(v___x_1151_, v___x_1170_);
lean_dec_ref(v___x_1170_);
lean_inc_n(v_a_1131_, 3);
v___x_1172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1172_, 0, v_a_1131_);
lean_ctor_set(v___x_1172_, 1, v___x_1150_);
lean_ctor_set(v___x_1172_, 2, v___x_1171_);
v___x_1173_ = l_Lean_Syntax_node1(v_a_1131_, v___x_1150_, v___x_1172_);
v___x_1174_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_1175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_a_1131_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_Syntax_node4(v_a_1131_, v___x_1162_, v___x_1165_, v___x_1173_, v___x_1175_, v_fst_1118_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1176_);
v___x_1178_ = v___x_1133_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_a_1129_);
lean_dec(v_a_1127_);
lean_dec(v_a_1125_);
lean_dec(v_fst_1118_);
lean_del_object(v___x_1116_);
lean_del_object(v___x_1112_);
lean_dec(v_a_1090_);
lean_dec(v_head_1075_);
v_a_1185_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1130_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1130_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_a_1127_);
lean_dec(v_a_1125_);
lean_dec(v_fst_1118_);
lean_del_object(v___x_1116_);
lean_del_object(v___x_1112_);
lean_dec(v_a_1090_);
lean_dec(v_head_1075_);
lean_dec_ref(v___f_1074_);
v_a_1193_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1128_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1128_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v_a_1125_);
lean_dec(v_fst_1118_);
lean_del_object(v___x_1116_);
lean_del_object(v___x_1112_);
lean_dec(v_a_1090_);
lean_dec(v_head_1075_);
lean_dec_ref(v___f_1074_);
v_a_1201_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1126_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1126_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v_fst_1118_);
lean_del_object(v___x_1116_);
lean_del_object(v___x_1112_);
lean_dec(v_a_1090_);
lean_dec(v_head_1075_);
lean_dec_ref(v___f_1074_);
v_a_1209_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1124_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1124_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_a_1090_);
lean_dec(v_numParams_1087_);
lean_dec(v_head_1075_);
lean_dec_ref(v___f_1074_);
lean_dec(v___x_1070_);
v_a_1224_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1106_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1106_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_numParams_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_xs_1076_);
lean_dec(v_head_1075_);
lean_dec_ref(v___f_1074_);
lean_dec(v_auxFunName_1073_);
lean_dec_ref(v_alts_1071_);
lean_dec(v___x_1070_);
lean_dec_ref(v_indVal_1069_);
v_a_1232_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1089_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1089_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v_xs_1076_);
lean_dec(v_head_1075_);
lean_dec_ref(v___f_1074_);
lean_dec(v_auxFunName_1073_);
lean_dec_ref(v_alts_1071_);
lean_dec(v___x_1070_);
lean_dec_ref(v_indVal_1069_);
v_a_1240_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1085_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1085_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___boxed(lean_object* v_indVal_1248_, lean_object* v___x_1249_, lean_object* v_alts_1250_, lean_object* v_numFields_1251_, lean_object* v_auxFunName_1252_, lean_object* v___f_1253_, lean_object* v_head_1254_, lean_object* v_xs_1255_, lean_object* v_type_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1(v_indVal_1248_, v___x_1249_, v_alts_1250_, v_numFields_1251_, v_auxFunName_1252_, v___f_1253_, v_head_1254_, v_xs_1255_, v_type_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v_numFields_1251_);
return v_res_1264_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_instMonadEIO(lean_box(0));
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(lean_object* v_msg_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v_toApplicative_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1373_; 
v___x_1280_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0);
v___x_1281_ = l_StateRefT_x27_instMonad___redArg(v___x_1280_);
v_toApplicative_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; 
v_unused_1374_ = lean_ctor_get(v___x_1281_, 1);
lean_dec(v_unused_1374_);
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1373_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_toApplicative_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1373_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_toFunctor_1286_; lean_object* v_toSeq_1287_; lean_object* v_toSeqLeft_1288_; lean_object* v_toSeqRight_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1371_; 
v_toFunctor_1286_ = lean_ctor_get(v_toApplicative_1282_, 0);
v_toSeq_1287_ = lean_ctor_get(v_toApplicative_1282_, 2);
v_toSeqLeft_1288_ = lean_ctor_get(v_toApplicative_1282_, 3);
v_toSeqRight_1289_ = lean_ctor_get(v_toApplicative_1282_, 4);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_toApplicative_1282_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v_toApplicative_1282_, 1);
lean_dec(v_unused_1372_);
v___x_1291_ = v_toApplicative_1282_;
v_isShared_1292_ = v_isSharedCheck_1371_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_toSeqRight_1289_);
lean_inc(v_toSeqLeft_1288_);
lean_inc(v_toSeq_1287_);
lean_inc(v_toFunctor_1286_);
lean_dec(v_toApplicative_1282_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1371_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___f_1293_; lean_object* v___f_1294_; lean_object* v___f_1295_; lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v___f_1298_; lean_object* v___f_1299_; lean_object* v___f_1300_; lean_object* v___x_1302_; 
v___f_1293_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1));
v___f_1294_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1286_);
v___f_1295_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1295_, 0, v_toFunctor_1286_);
v___f_1296_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1296_, 0, v_toFunctor_1286_);
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___f_1295_);
lean_ctor_set(v___x_1297_, 1, v___f_1296_);
v___f_1298_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1298_, 0, v_toSeqRight_1289_);
v___f_1299_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1299_, 0, v_toSeqLeft_1288_);
v___f_1300_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1300_, 0, v_toSeq_1287_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v___f_1298_);
lean_ctor_set(v___x_1291_, 3, v___f_1299_);
lean_ctor_set(v___x_1291_, 2, v___f_1300_);
lean_ctor_set(v___x_1291_, 1, v___f_1293_);
lean_ctor_set(v___x_1291_, 0, v___x_1297_);
v___x_1302_ = v___x_1291_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___f_1293_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v___f_1300_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v___f_1299_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v___f_1298_);
v___x_1302_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1304_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v___f_1294_);
lean_ctor_set(v___x_1284_, 0, v___x_1302_);
v___x_1304_ = v___x_1284_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___f_1294_);
v___x_1304_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; lean_object* v_toApplicative_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1367_; 
v___x_1305_ = l_StateRefT_x27_instMonad___redArg(v___x_1304_);
v_toApplicative_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v___x_1305_, 1);
lean_dec(v_unused_1368_);
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1367_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_toApplicative_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1367_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_toFunctor_1310_; lean_object* v_toSeq_1311_; lean_object* v_toSeqLeft_1312_; lean_object* v_toSeqRight_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1365_; 
v_toFunctor_1310_ = lean_ctor_get(v_toApplicative_1306_, 0);
v_toSeq_1311_ = lean_ctor_get(v_toApplicative_1306_, 2);
v_toSeqLeft_1312_ = lean_ctor_get(v_toApplicative_1306_, 3);
v_toSeqRight_1313_ = lean_ctor_get(v_toApplicative_1306_, 4);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_toApplicative_1306_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v_toApplicative_1306_, 1);
lean_dec(v_unused_1366_);
v___x_1315_ = v_toApplicative_1306_;
v_isShared_1316_ = v_isSharedCheck_1365_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_toSeqRight_1313_);
lean_inc(v_toSeqLeft_1312_);
lean_inc(v_toSeq_1311_);
lean_inc(v_toFunctor_1310_);
lean_dec(v_toApplicative_1306_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1365_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___f_1317_; lean_object* v___f_1318_; lean_object* v___f_1319_; lean_object* v___f_1320_; lean_object* v___x_1321_; lean_object* v___f_1322_; lean_object* v___f_1323_; lean_object* v___f_1324_; lean_object* v___x_1326_; 
v___f_1317_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3));
v___f_1318_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1310_);
v___f_1319_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1319_, 0, v_toFunctor_1310_);
v___f_1320_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1320_, 0, v_toFunctor_1310_);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___f_1319_);
lean_ctor_set(v___x_1321_, 1, v___f_1320_);
v___f_1322_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1322_, 0, v_toSeqRight_1313_);
v___f_1323_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1323_, 0, v_toSeqLeft_1312_);
v___f_1324_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1324_, 0, v_toSeq_1311_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v___f_1322_);
lean_ctor_set(v___x_1315_, 3, v___f_1323_);
lean_ctor_set(v___x_1315_, 2, v___f_1324_);
lean_ctor_set(v___x_1315_, 1, v___f_1317_);
lean_ctor_set(v___x_1315_, 0, v___x_1321_);
v___x_1326_ = v___x_1315_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___f_1317_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v___f_1324_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v___f_1323_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v___f_1322_);
v___x_1326_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v___f_1318_);
lean_ctor_set(v___x_1308_, 0, v___x_1326_);
v___x_1328_ = v___x_1308_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___f_1318_);
v___x_1328_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v_toApplicative_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1361_; 
v___x_1329_ = l_StateRefT_x27_instMonad___redArg(v___x_1328_);
v_toApplicative_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v___x_1329_, 1);
lean_dec(v_unused_1362_);
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1361_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_toApplicative_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1361_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v_toFunctor_1334_; lean_object* v_toSeq_1335_; lean_object* v_toSeqLeft_1336_; lean_object* v_toSeqRight_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1359_; 
v_toFunctor_1334_ = lean_ctor_get(v_toApplicative_1330_, 0);
v_toSeq_1335_ = lean_ctor_get(v_toApplicative_1330_, 2);
v_toSeqLeft_1336_ = lean_ctor_get(v_toApplicative_1330_, 3);
v_toSeqRight_1337_ = lean_ctor_get(v_toApplicative_1330_, 4);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_toApplicative_1330_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v_toApplicative_1330_, 1);
lean_dec(v_unused_1360_);
v___x_1339_ = v_toApplicative_1330_;
v_isShared_1340_ = v_isSharedCheck_1359_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_toSeqRight_1337_);
lean_inc(v_toSeqLeft_1336_);
lean_inc(v_toSeq_1335_);
lean_inc(v_toFunctor_1334_);
lean_dec(v_toApplicative_1330_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1359_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___f_1341_; lean_object* v___f_1342_; lean_object* v___f_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; lean_object* v___f_1346_; lean_object* v___f_1347_; lean_object* v___f_1348_; lean_object* v___x_1350_; 
v___f_1341_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5));
v___f_1342_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1334_);
v___f_1343_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1343_, 0, v_toFunctor_1334_);
v___f_1344_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1344_, 0, v_toFunctor_1334_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___f_1343_);
lean_ctor_set(v___x_1345_, 1, v___f_1344_);
v___f_1346_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1346_, 0, v_toSeqRight_1337_);
v___f_1347_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1347_, 0, v_toSeqLeft_1336_);
v___f_1348_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1348_, 0, v_toSeq_1335_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 4, v___f_1346_);
lean_ctor_set(v___x_1339_, 3, v___f_1347_);
lean_ctor_set(v___x_1339_, 2, v___f_1348_);
lean_ctor_set(v___x_1339_, 1, v___f_1341_);
lean_ctor_set(v___x_1339_, 0, v___x_1345_);
v___x_1350_ = v___x_1339_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___f_1341_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v___f_1348_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v___f_1347_);
lean_ctor_set(v_reuseFailAlloc_1358_, 4, v___f_1346_);
v___x_1350_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 1, v___f_1342_);
lean_ctor_set(v___x_1332_, 0, v___x_1350_);
v___x_1352_ = v___x_1332_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v___f_1342_);
v___x_1352_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_49115__overap_1355_; lean_object* v___x_1356_; 
v___x_1353_ = lean_box(0);
v___x_1354_ = l_instInhabitedOfMonad___redArg(v___x_1352_, v___x_1353_);
v___x_49115__overap_1355_ = lean_panic_fn_borrowed(v___x_1354_, v_msg_1272_);
lean_dec(v___x_1354_);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
v___x_1356_ = lean_apply_7(v___x_49115__overap_1355_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, lean_box(0));
return v___x_1356_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(v_msg_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(lean_object* v_opts_1384_, lean_object* v_opt_1385_){
_start:
{
lean_object* v_name_1386_; lean_object* v_defValue_1387_; lean_object* v_map_1388_; lean_object* v___x_1389_; 
v_name_1386_ = lean_ctor_get(v_opt_1385_, 0);
v_defValue_1387_ = lean_ctor_get(v_opt_1385_, 1);
v_map_1388_ = lean_ctor_get(v_opts_1384_, 0);
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1388_, v_name_1386_);
if (lean_obj_tag(v___x_1389_) == 0)
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_unbox(v_defValue_1387_);
return v___x_1390_;
}
else
{
lean_object* v_val_1391_; 
v_val_1391_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_val_1391_);
lean_dec_ref(v___x_1389_);
if (lean_obj_tag(v_val_1391_) == 1)
{
uint8_t v_v_1392_; 
v_v_1392_ = lean_ctor_get_uint8(v_val_1391_, 0);
lean_dec_ref(v_val_1391_);
return v_v_1392_;
}
else
{
uint8_t v___x_1393_; 
lean_dec(v_val_1391_);
v___x_1393_ = lean_unbox(v_defValue_1387_);
return v___x_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_opts_1394_, lean_object* v_opt_1395_){
_start:
{
uint8_t v_res_1396_; lean_object* v_r_1397_; 
v_res_1396_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v_opts_1394_, v_opt_1395_);
lean_dec_ref(v_opt_1395_);
lean_dec_ref(v_opts_1394_);
v_r_1397_ = lean_box(v_res_1396_);
return v_r_1397_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_box(1);
v___x_1399_ = l_Lean_MessageData_ofFormat(v___x_1398_);
return v___x_1399_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2));
v___x_1404_ = l_Lean_MessageData_ofFormat(v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
if (lean_obj_tag(v_x_1406_) == 0)
{
return v_x_1405_;
}
else
{
lean_object* v_head_1407_; lean_object* v_tail_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1430_; 
v_head_1407_ = lean_ctor_get(v_x_1406_, 0);
v_tail_1408_ = lean_ctor_get(v_x_1406_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1410_ = v_x_1406_;
v_isShared_1411_ = v_isSharedCheck_1430_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_tail_1408_);
lean_inc(v_head_1407_);
lean_dec(v_x_1406_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1430_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_before_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1428_; 
v_before_1412_ = lean_ctor_get(v_head_1407_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_head_1407_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v_head_1407_, 1);
lean_dec(v_unused_1429_);
v___x_1414_ = v_head_1407_;
v_isShared_1415_ = v_isSharedCheck_1428_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_before_1412_);
lean_dec(v_head_1407_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1428_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_1415_ == 0)
{
lean_ctor_set_tag(v___x_1414_, 7);
lean_ctor_set(v___x_1414_, 1, v___x_1416_);
lean_ctor_set(v___x_1414_, 0, v_x_1405_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_x_1405_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3);
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 7);
lean_ctor_set(v___x_1410_, 1, v___x_1419_);
lean_ctor_set(v___x_1410_, 0, v___x_1418_);
v___x_1421_ = v___x_1410_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = l_Lean_MessageData_ofSyntax(v_before_1412_);
v___x_1423_ = l_Lean_indentD(v___x_1422_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1421_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v_x_1405_ = v___x_1424_;
v_x_1406_ = v_tail_1408_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_1435_ = l_Lean_MessageData_ofFormat(v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_1436_, lean_object* v_macroStack_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_options_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_options_1440_ = lean_ctor_get(v___y_1438_, 2);
v___x_1441_ = l_Lean_Elab_pp_macroStack;
v___x_1442_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v_options_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec(v_macroStack_1437_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_msgData_1436_);
return v___x_1443_;
}
else
{
if (lean_obj_tag(v_macroStack_1437_) == 0)
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_msgData_1436_);
return v___x_1444_;
}
else
{
lean_object* v_head_1445_; lean_object* v_after_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1461_; 
v_head_1445_ = lean_ctor_get(v_macroStack_1437_, 0);
lean_inc(v_head_1445_);
v_after_1446_ = lean_ctor_get(v_head_1445_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_head_1445_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_head_1445_, 0);
lean_dec(v_unused_1462_);
v___x_1448_ = v_head_1445_;
v_isShared_1449_ = v_isSharedCheck_1461_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_after_1446_);
lean_dec(v_head_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1461_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_1449_ == 0)
{
lean_ctor_set_tag(v___x_1448_, 7);
lean_ctor_set(v___x_1448_, 1, v___x_1450_);
lean_ctor_set(v___x_1448_, 0, v_msgData_1436_);
v___x_1452_ = v___x_1448_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_msgData_1436_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v_msgData_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1453_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_1454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1452_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
v___x_1455_ = l_Lean_MessageData_ofSyntax(v_after_1446_);
v___x_1456_ = l_Lean_indentD(v___x_1455_);
v_msgData_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1457_, 0, v___x_1454_);
lean_ctor_set(v_msgData_1457_, 1, v___x_1456_);
v___x_1458_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_msgData_1457_, v_macroStack_1437_);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_1463_, lean_object* v_macroStack_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1463_, v_macroStack_1464_, v___y_1465_);
lean_dec_ref(v___y_1465_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v_env_1475_; lean_object* v___x_1476_; lean_object* v_mctx_1477_; lean_object* v_lctx_1478_; lean_object* v_options_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1474_ = lean_st_ref_get(v___y_1472_);
v_env_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc_ref(v_env_1475_);
lean_dec(v___x_1474_);
v___x_1476_ = lean_st_ref_get(v___y_1470_);
v_mctx_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc_ref(v_mctx_1477_);
lean_dec(v___x_1476_);
v_lctx_1478_ = lean_ctor_get(v___y_1469_, 2);
v_options_1479_ = lean_ctor_get(v___y_1471_, 2);
lean_inc_ref(v_options_1479_);
lean_inc_ref(v_lctx_1478_);
v___x_1480_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1480_, 0, v_env_1475_);
lean_ctor_set(v___x_1480_, 1, v_mctx_1477_);
lean_ctor_set(v___x_1480_, 2, v_lctx_1478_);
lean_ctor_set(v___x_1480_, 3, v_options_1479_);
v___x_1481_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v_msgData_1468_);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msgData_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_ref_1498_; lean_object* v___x_1499_; lean_object* v_a_1500_; lean_object* v_macroStack_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1512_; 
v_ref_1498_ = lean_ctor_get(v___y_1495_, 5);
v___x_1499_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_1490_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref(v___x_1499_);
v_macroStack_1501_ = lean_ctor_get(v___y_1491_, 1);
lean_inc_n(v_macroStack_1501_, 2);
v___x_1502_ = l_Lean_Elab_getBetterRef(v_ref_1498_, v_macroStack_1501_);
v___x_1503_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_1500_, v_macroStack_1501_, v___y_1495_);
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1512_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1512_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1502_);
lean_ctor_set(v___x_1508_, 1, v_a_1504_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set_tag(v___x_1506_, 1);
lean_ctor_set(v___x_1506_, 0, v___x_1508_);
v___x_1510_ = v___x_1506_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
return v_res_1521_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__0));
v___x_1524_ = l_Lean_stringToMessageData(v___x_1523_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__2));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1531_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__6));
v___x_1532_ = lean_unsigned_to_nat(11u);
v___x_1533_ = lean_unsigned_to_nat(122u);
v___x_1534_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__5));
v___x_1535_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__4));
v___x_1536_ = l_mkPanicMessageWithDecl(v___x_1535_, v___x_1534_, v___x_1533_, v___x_1532_, v___x_1531_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(lean_object* v_constName_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1553_; lean_object* v_env_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; 
v___x_1553_ = lean_st_ref_get(v___y_1543_);
v_env_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc_ref(v_env_1554_);
lean_dec(v___x_1553_);
v___x_1555_ = 0;
lean_inc(v_constName_1537_);
v___x_1556_ = l_Lean_Environment_findAsync_x3f(v_env_1554_, v_constName_1537_, v___x_1555_);
if (lean_obj_tag(v___x_1556_) == 1)
{
lean_object* v_val_1557_; uint8_t v_kind_1558_; 
v_val_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_val_1557_);
lean_dec_ref(v___x_1556_);
v_kind_1558_ = lean_ctor_get_uint8(v_val_1557_, sizeof(void*)*3);
if (v_kind_1558_ == 6)
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1557_);
if (lean_obj_tag(v___x_1559_) == 6)
{
lean_object* v_val_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_constName_1537_);
v_val_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_val_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set_tag(v___x_1562_, 0);
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_val_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_dec_ref(v___x_1559_);
v___x_1568_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7);
v___x_1569_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(v___x_1568_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1578_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
if (lean_obj_tag(v_a_1570_) == 0)
{
lean_del_object(v___x_1572_);
goto v___jp_1545_;
}
else
{
lean_object* v_val_1574_; lean_object* v___x_1576_; 
lean_dec(v_constName_1537_);
v_val_1574_ = lean_ctor_get(v_a_1570_, 0);
lean_inc(v_val_1574_);
lean_dec_ref(v_a_1570_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v_val_1574_);
v___x_1576_ = v___x_1572_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_val_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_constName_1537_);
v_a_1579_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1569_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1569_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
else
{
lean_dec(v_val_1557_);
goto v___jp_1545_;
}
}
else
{
lean_dec(v___x_1556_);
goto v___jp_1545_;
}
v___jp_1545_:
{
lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1546_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_1547_ = 0;
v___x_1548_ = l_Lean_MessageData_ofConstName(v_constName_1537_, v___x_1547_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1546_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v___x_1551_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___boxed(lean_object* v_constName_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v_constName_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(lean_object* v_indVal_1597_, lean_object* v_auxFunName_1598_, lean_object* v_as_x27_1599_, lean_object* v_b_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
if (lean_obj_tag(v_as_x27_1599_) == 0)
{
lean_object* v___x_1608_; 
lean_dec(v_auxFunName_1598_);
lean_dec_ref(v_indVal_1597_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_b_1600_);
return v___x_1608_;
}
else
{
lean_object* v_head_1609_; lean_object* v_tail_1610_; lean_object* v___x_1611_; 
v_head_1609_ = lean_ctor_get(v_as_x27_1599_, 0);
lean_inc_n(v_head_1609_, 2);
v_tail_1610_ = lean_ctor_get(v_as_x27_1599_, 1);
lean_inc(v_tail_1610_);
lean_dec_ref(v_as_x27_1599_);
v___x_1611_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v_head_1609_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v_toConstantVal_1613_; lean_object* v_numFields_1614_; lean_object* v_type_1615_; lean_object* v___f_1616_; lean_object* v___x_1617_; lean_object* v_alts_1618_; lean_object* v___f_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref(v___x_1611_);
v_toConstantVal_1613_ = lean_ctor_get(v_a_1612_, 0);
lean_inc_ref(v_toConstantVal_1613_);
v_numFields_1614_ = lean_ctor_get(v_a_1612_, 4);
lean_inc(v_numFields_1614_);
lean_dec(v_a_1612_);
v_type_1615_ = lean_ctor_get(v_toConstantVal_1613_, 2);
lean_inc_ref(v_type_1615_);
lean_dec_ref(v_toConstantVal_1613_);
v___f_1616_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0));
v___x_1617_ = lean_unsigned_to_nat(0u);
v_alts_1618_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
lean_inc(v_auxFunName_1598_);
lean_inc_ref(v_indVal_1597_);
v___f_1619_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___boxed), 16, 7);
lean_closure_set(v___f_1619_, 0, v_indVal_1597_);
lean_closure_set(v___f_1619_, 1, v___x_1617_);
lean_closure_set(v___f_1619_, 2, v_alts_1618_);
lean_closure_set(v___f_1619_, 3, v_numFields_1614_);
lean_closure_set(v___f_1619_, 4, v_auxFunName_1598_);
lean_closure_set(v___f_1619_, 5, v___f_1616_);
lean_closure_set(v___f_1619_, 6, v_head_1609_);
v___x_1620_ = 0;
v___x_1621_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_1615_, v___f_1619_, v___x_1620_, v___x_1620_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref(v___x_1621_);
v___x_1623_ = lean_array_push(v_b_1600_, v_a_1622_);
v_as_x27_1599_ = v_tail_1610_;
v_b_1600_ = v___x_1623_;
goto _start;
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec(v_tail_1610_);
lean_dec_ref(v_b_1600_);
lean_dec(v_auxFunName_1598_);
lean_dec_ref(v_indVal_1597_);
v_a_1625_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1621_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1621_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_tail_1610_);
lean_dec(v_head_1609_);
lean_dec_ref(v_b_1600_);
lean_dec(v_auxFunName_1598_);
lean_dec_ref(v_indVal_1597_);
v_a_1633_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1611_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1611_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object* v_indVal_1641_, lean_object* v_auxFunName_1642_, lean_object* v_as_x27_1643_, lean_object* v_b_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1641_, v_auxFunName_1642_, v_as_x27_1643_, v_b_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(size_t v_sz_1653_, size_t v_i_1654_, lean_object* v_bs_1655_){
_start:
{
uint8_t v___x_1656_; 
v___x_1656_ = lean_usize_dec_lt(v_i_1654_, v_sz_1653_);
if (v___x_1656_ == 0)
{
return v_bs_1655_;
}
else
{
lean_object* v_v_1657_; lean_object* v___x_1658_; lean_object* v_bs_x27_1659_; size_t v___x_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v_v_1657_ = lean_array_uget(v_bs_1655_, v_i_1654_);
v___x_1658_ = lean_unsigned_to_nat(0u);
v_bs_x27_1659_ = lean_array_uset(v_bs_1655_, v_i_1654_, v___x_1658_);
v___x_1660_ = ((size_t)1ULL);
v___x_1661_ = lean_usize_add(v_i_1654_, v___x_1660_);
v___x_1662_ = lean_array_uset(v_bs_x27_1659_, v_i_1654_, v_v_1657_);
v_i_1654_ = v___x_1661_;
v_bs_1655_ = v___x_1662_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6___boxed(lean_object* v_sz_1664_, lean_object* v_i_1665_, lean_object* v_bs_1666_){
_start:
{
size_t v_sz_boxed_1667_; size_t v_i_boxed_1668_; lean_object* v_res_1669_; 
v_sz_boxed_1667_ = lean_unbox_usize(v_sz_1664_);
lean_dec(v_sz_1664_);
v_i_boxed_1668_ = lean_unbox_usize(v_i_1665_);
lean_dec(v_i_1665_);
v_res_1669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(v_sz_boxed_1667_, v_i_boxed_1668_, v_bs_1666_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(lean_object* v_indVal_1670_, lean_object* v_auxFunName_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_ctors_1679_; lean_object* v_alts_1680_; lean_object* v___x_1681_; 
v_ctors_1679_ = lean_ctor_get(v_indVal_1670_, 4);
v_alts_1680_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
lean_inc(v_ctors_1679_);
lean_inc_ref(v_indVal_1670_);
v___x_1681_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1670_, v_auxFunName_1671_, v_ctors_1679_, v_alts_1680_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1683_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(v_indVal_1670_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
lean_dec_ref(v_indVal_1670_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1695_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1695_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1695_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; size_t v_sz_1689_; size_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1688_ = lean_array_push(v_a_1682_, v_a_1684_);
v_sz_1689_ = lean_array_size(v___x_1688_);
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(v_sz_1689_, v___x_1690_, v___x_1688_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1691_);
v___x_1693_ = v___x_1686_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_a_1682_);
v_a_1696_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1683_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1683_);
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
else
{
lean_dec_ref(v_indVal_1670_);
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts___boxed(lean_object* v_indVal_1704_, lean_object* v_auxFunName_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(v_indVal_1704_, v_auxFunName_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1(lean_object* v_upperBound_1714_, lean_object* v_inst_1715_, lean_object* v_R_1716_, lean_object* v_a_1717_, lean_object* v_b_1718_, lean_object* v_c_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_upperBound_1714_, v_a_1717_, v_b_1718_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___boxed(lean_object* v_upperBound_1728_, lean_object* v_inst_1729_, lean_object* v_R_1730_, lean_object* v_a_1731_, lean_object* v_b_1732_, lean_object* v_c_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1(v_upperBound_1728_, v_inst_1729_, v_R_1730_, v_a_1731_, v_b_1732_, v_c_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v_upperBound_1728_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2(lean_object* v___x_1742_, lean_object* v_as_1743_, size_t v_i_1744_, size_t v_stop_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_1742_, v_as_1743_, v_i_1744_, v_stop_1745_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___boxed(lean_object* v___x_1754_, lean_object* v_as_1755_, lean_object* v_i_1756_, lean_object* v_stop_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
size_t v_i_boxed_1765_; size_t v_stop_boxed_1766_; lean_object* v_res_1767_; 
v_i_boxed_1765_ = lean_unbox_usize(v_i_1756_);
lean_dec(v_i_1756_);
v_stop_boxed_1766_ = lean_unbox_usize(v_stop_1757_);
lean_dec(v_stop_1757_);
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2(v___x_1754_, v_as_1755_, v_i_boxed_1765_, v_stop_boxed_1766_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v_as_1755_);
lean_dec_ref(v___x_1754_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3(lean_object* v_upperBound_1768_, lean_object* v_indVal_1769_, lean_object* v___x_1770_, lean_object* v_xs_1771_, lean_object* v_a_1772_, lean_object* v_auxFunName_1773_, lean_object* v_inst_1774_, lean_object* v_R_1775_, lean_object* v_a_1776_, lean_object* v_b_1777_, lean_object* v_c_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_1768_, v_indVal_1769_, v___x_1770_, v_xs_1771_, v_a_1772_, v_auxFunName_1773_, v_a_1776_, v_b_1777_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1787_ = _args[0];
lean_object* v_indVal_1788_ = _args[1];
lean_object* v___x_1789_ = _args[2];
lean_object* v_xs_1790_ = _args[3];
lean_object* v_a_1791_ = _args[4];
lean_object* v_auxFunName_1792_ = _args[5];
lean_object* v_inst_1793_ = _args[6];
lean_object* v_R_1794_ = _args[7];
lean_object* v_a_1795_ = _args[8];
lean_object* v_b_1796_ = _args[9];
lean_object* v_c_1797_ = _args[10];
lean_object* v___y_1798_ = _args[11];
lean_object* v___y_1799_ = _args[12];
lean_object* v___y_1800_ = _args[13];
lean_object* v___y_1801_ = _args[14];
lean_object* v___y_1802_ = _args[15];
lean_object* v___y_1803_ = _args[16];
lean_object* v___y_1804_ = _args[17];
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3(v_upperBound_1787_, v_indVal_1788_, v___x_1789_, v_xs_1790_, v_a_1791_, v_auxFunName_1792_, v_inst_1793_, v_R_1794_, v_a_1795_, v_b_1796_, v_c_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec_ref(v_a_1791_);
lean_dec(v___x_1789_);
lean_dec(v_upperBound_1787_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5(lean_object* v_indVal_1806_, lean_object* v_auxFunName_1807_, lean_object* v_as_1808_, lean_object* v_as_x27_1809_, lean_object* v_b_1810_, lean_object* v_a_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1806_, v_auxFunName_1807_, v_as_x27_1809_, v_b_1810_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___boxed(lean_object* v_indVal_1820_, lean_object* v_auxFunName_1821_, lean_object* v_as_1822_, lean_object* v_as_x27_1823_, lean_object* v_b_1824_, lean_object* v_a_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5(v_indVal_1820_, v_auxFunName_1821_, v_as_1822_, v_as_x27_1823_, v_b_1824_, v_a_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_as_1822_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1834_, lean_object* v_msg_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1844_, lean_object* v_msg_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0(v_00_u03b1_1844_, v_msg_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1854_, lean_object* v_macroStack_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1854_, v_macroStack_1855_, v___y_1860_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1864_, lean_object* v_macroStack_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(v_msgData_1864_, v_macroStack_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(lean_object* v_header_1887_, lean_object* v_indVal_1888_, lean_object* v_auxFunName_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v___x_1897_; 
lean_inc_ref(v_indVal_1888_);
v___x_1897_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_1887_, v_indVal_1888_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(v_indVal_1888_, v_auxFunName_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1930_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1930_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1930_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_ref_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; size_t v_sz_1913_; size_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v_ref_1904_ = lean_ctor_get(v_a_1894_, 5);
v___x_1905_ = 0;
v___x_1906_ = l_Lean_SourceInfo_fromRef(v_ref_1904_, v___x_1905_);
v___x_1907_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0));
v___x_1908_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1));
lean_inc_n(v___x_1906_, 6);
v___x_1909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1906_);
lean_ctor_set(v___x_1909_, 1, v___x_1907_);
v___x_1910_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_1911_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_1912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1906_);
lean_ctor_set(v___x_1912_, 1, v___x_1910_);
lean_ctor_set(v___x_1912_, 2, v___x_1911_);
v_sz_1913_ = lean_array_size(v_a_1898_);
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_1913_, v___x_1914_, v_a_1898_);
v___x_1916_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_1917_ = l_Lean_mkSepArray(v___x_1915_, v___x_1916_);
lean_dec_ref(v___x_1915_);
v___x_1918_ = l_Array_append___redArg(v___x_1911_, v___x_1917_);
lean_dec_ref(v___x_1917_);
v___x_1919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1906_);
lean_ctor_set(v___x_1919_, 1, v___x_1910_);
lean_ctor_set(v___x_1919_, 2, v___x_1918_);
v___x_1920_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2));
v___x_1921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1906_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4));
v___x_1923_ = l_Array_append___redArg(v___x_1911_, v_a_1900_);
lean_dec(v_a_1900_);
v___x_1924_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1906_);
lean_ctor_set(v___x_1924_, 1, v___x_1910_);
lean_ctor_set(v___x_1924_, 2, v___x_1923_);
v___x_1925_ = l_Lean_Syntax_node1(v___x_1906_, v___x_1922_, v___x_1924_);
lean_inc_ref(v___x_1912_);
v___x_1926_ = l_Lean_Syntax_node6(v___x_1906_, v___x_1908_, v___x_1909_, v___x_1912_, v___x_1912_, v___x_1919_, v___x_1921_, v___x_1925_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1926_);
v___x_1928_ = v___x_1902_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_a_1898_);
v_a_1931_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1899_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1899_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_auxFunName_1889_);
lean_dec_ref(v_indVal_1888_);
v_a_1939_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1897_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1897_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___boxed(lean_object* v_header_1947_, lean_object* v_indVal_1948_, lean_object* v_auxFunName_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(v_header_1947_, v_indVal_1948_, v_auxFunName_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
return v_res_1957_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(lean_object* v_msg_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_44350__overap_1968_; lean_object* v___x_1969_; 
v___x_1967_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0);
v___x_44350__overap_1968_ = lean_panic_fn_borrowed(v___x_1967_, v_msg_1959_);
lean_inc(v___y_1965_);
lean_inc_ref(v___y_1964_);
lean_inc(v___y_1963_);
lean_inc_ref(v___y_1962_);
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
v___x_1969_ = lean_apply_7(v___x_44350__overap_1968_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, lean_box(0));
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___boxed(lean_object* v_msg_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(v_msg_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(lean_object* v___x_1979_, lean_object* v_as_1980_, size_t v_i_1981_, size_t v_stop_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_usize_dec_eq(v_i_1981_, v_stop_1982_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_array_uget_borrowed(v_as_1980_, v_i_1981_);
lean_inc(v___y_1986_);
lean_inc_ref(v___y_1985_);
lean_inc(v___y_1984_);
lean_inc_ref(v___y_1983_);
lean_inc(v___x_1989_);
v___x_1990_ = lean_infer_type(v___x_1989_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2003_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2003_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2003_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
uint8_t v___x_1995_; 
v___x_1995_ = l_Lean_Expr_containsFVar(v_a_1991_, v___x_1979_);
lean_dec(v_a_1991_);
if (v___x_1995_ == 0)
{
size_t v___x_1996_; size_t v___x_1997_; 
lean_del_object(v___x_1993_);
v___x_1996_ = ((size_t)1ULL);
v___x_1997_ = lean_usize_add(v_i_1981_, v___x_1996_);
v_i_1981_ = v___x_1997_;
goto _start;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_box(v___x_1995_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1999_);
v___x_2001_ = v___x_1993_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_a_2004_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1990_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1990_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
uint8_t v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = 0;
v___x_2013_ = lean_box(v___x_2012_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg___boxed(lean_object* v___x_2015_, lean_object* v_as_2016_, lean_object* v_i_2017_, lean_object* v_stop_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
size_t v_i_boxed_2024_; size_t v_stop_boxed_2025_; lean_object* v_res_2026_; 
v_i_boxed_2024_ = lean_unbox_usize(v_i_2017_);
lean_dec(v_i_2017_);
v_stop_boxed_2025_ = lean_unbox_usize(v_stop_2018_);
lean_dec(v_stop_2018_);
v_res_2026_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_2015_, v_as_2016_, v_i_boxed_2024_, v_stop_boxed_2025_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec_ref(v_as_2016_);
lean_dec(v___x_2015_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(lean_object* v_upperBound_2028_, lean_object* v_indVal_2029_, lean_object* v___x_2030_, lean_object* v_xs_2031_, lean_object* v_a_2032_, lean_object* v___x_2033_, lean_object* v_auxFunName_2034_, lean_object* v_a_2035_, lean_object* v_b_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
uint8_t v___x_2044_; 
v___x_2044_ = lean_nat_dec_lt(v_a_2035_, v_upperBound_2028_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; 
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_b_2036_);
return v___x_2045_;
}
else
{
lean_object* v_snd_2046_; lean_object* v_snd_2047_; lean_object* v_fst_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2389_; 
v_snd_2046_ = lean_ctor_get(v_b_2036_, 1);
lean_inc(v_snd_2046_);
v_snd_2047_ = lean_ctor_get(v_snd_2046_, 1);
lean_inc(v_snd_2047_);
v_fst_2048_ = lean_ctor_get(v_b_2036_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_b_2036_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; 
v_unused_2390_ = lean_ctor_get(v_b_2036_, 1);
lean_dec(v_unused_2390_);
v___x_2050_ = v_b_2036_;
v_isShared_2051_ = v_isSharedCheck_2389_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_fst_2048_);
lean_dec(v_b_2036_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2389_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v_fst_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2387_; 
v_fst_2052_ = lean_ctor_get(v_snd_2046_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_snd_2046_);
if (v_isSharedCheck_2387_ == 0)
{
lean_object* v_unused_2388_; 
v_unused_2388_ = lean_ctor_get(v_snd_2046_, 1);
lean_dec(v_unused_2388_);
v___x_2054_ = v_snd_2046_;
v_isShared_2055_ = v_isSharedCheck_2387_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_fst_2052_);
lean_dec(v_snd_2046_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2387_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_fst_2056_; lean_object* v_snd_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2386_; 
v_fst_2056_ = lean_ctor_get(v_snd_2047_, 0);
v_snd_2057_ = lean_ctor_get(v_snd_2047_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_snd_2047_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2059_ = v_snd_2047_;
v_isShared_2060_ = v_isSharedCheck_2386_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_snd_2057_);
lean_inc(v_fst_2056_);
lean_dec(v_snd_2047_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2386_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_numParams_2061_; lean_object* v___x_2062_; lean_object* v_a_2064_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_numParams_2061_ = lean_ctor_get(v_indVal_2029_, 1);
v___x_2062_ = lean_unsigned_to_nat(1u);
v___x_2067_ = lean_nat_add(v_numParams_2061_, v___x_2030_);
v___x_2068_ = lean_nat_sub(v___x_2067_, v_a_2035_);
lean_dec(v___x_2067_);
v___x_2069_ = lean_nat_sub(v___x_2068_, v___x_2062_);
lean_dec(v___x_2068_);
v___x_2070_ = l_Lean_instInhabitedExpr;
v___x_2071_ = lean_array_get_borrowed(v___x_2070_, v_xs_2031_, v___x_2069_);
v___x_2072_ = l_Lean_Expr_fvarId_x21(v___x_2071_);
v___x_2073_ = l_Lean_Expr_containsFVar(v_a_2032_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; 
lean_inc(v___x_2072_);
v___x_2074_ = l_Lean_FVarId_getUserName___redArg(v___x_2072_, v___y_2039_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2076_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc_n(v_a_2075_, 2);
lean_dec_ref(v___x_2074_);
v___x_2076_ = l_Lean_Core_mkFreshUserName(v_a_2075_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___x_2076_);
v___x_2078_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___closed__0));
v___x_2079_ = lean_name_append_after(v_a_2075_, v___x_2078_);
v___x_2080_ = l_Lean_Core_mkFreshUserName(v___x_2079_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2082_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref(v___x_2080_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___x_2071_);
v___x_2082_ = lean_infer_type(v___x_2071_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2084_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc_n(v_a_2083_, 2);
lean_dec_ref(v___x_2082_);
v___x_2084_ = l_Lean_Meta_isProp(v_a_2083_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
v___x_2086_ = lean_mk_syntax_ident(v_a_2077_);
v___x_2087_ = lean_mk_syntax_ident(v_a_2081_);
lean_inc(v___x_2086_);
v___x_2088_ = lean_array_push(v_fst_2048_, v___x_2086_);
lean_inc(v___x_2087_);
v___x_2089_ = lean_array_push(v_fst_2052_, v___x_2087_);
v___x_2090_ = lean_unbox(v_a_2085_);
if (v___x_2090_ == 0)
{
uint8_t v___x_2091_; uint8_t v_a_2093_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v_lower_2259_; lean_object* v_upper_2260_; 
v___x_2091_ = l_Lean_Expr_isAppOf(v_a_2083_, v___x_2033_);
lean_dec(v_a_2083_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
lean_dec(v_a_2085_);
v___x_2268_ = lean_nat_add(v___x_2069_, v___x_2062_);
lean_dec(v___x_2069_);
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = lean_array_get_size(v_xs_2031_);
v___x_2271_ = lean_nat_dec_le(v___x_2268_, v___x_2269_);
if (v___x_2271_ == 0)
{
v_lower_2259_ = v___x_2268_;
v_upper_2260_ = v___x_2270_;
goto v___jp_2258_;
}
else
{
lean_dec(v___x_2268_);
v_lower_2259_ = v___x_2269_;
v_upper_2260_ = v___x_2270_;
goto v___jp_2258_;
}
}
else
{
uint8_t v___x_2272_; 
lean_dec(v___x_2072_);
lean_dec(v___x_2069_);
lean_del_object(v___x_2059_);
lean_del_object(v___x_2054_);
lean_del_object(v___x_2050_);
v___x_2272_ = lean_unbox(v_snd_2057_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; 
lean_dec(v_a_2085_);
v___x_2273_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc_n(v_a_2274_, 4);
lean_dec_ref(v___x_2273_);
v___x_2275_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_2276_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_2034_);
v___x_2277_ = lean_mk_syntax_ident(v_auxFunName_2034_);
v___x_2278_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2279_ = l_Lean_Syntax_node2(v_a_2274_, v___x_2278_, v___x_2086_, v___x_2087_);
v___x_2280_ = l_Lean_Syntax_node2(v_a_2274_, v___x_2276_, v___x_2277_, v___x_2279_);
v___x_2281_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_2282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2282_, 0, v_a_2274_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = l_Lean_Syntax_node3(v_a_2274_, v___x_2275_, v___x_2280_, v___x_2282_, v_fst_2056_);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set(v___x_2284_, 1, v_snd_2057_);
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2089_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2088_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v_a_2064_ = v___x_2286_;
goto v___jp_2063_;
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
lean_dec(v___x_2087_);
lean_dec(v___x_2086_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2287_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2273_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2273_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
else
{
lean_object* v___x_2295_; 
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
v___x_2295_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc_n(v_a_2296_, 2);
lean_dec_ref(v___x_2295_);
v___x_2297_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_2034_);
v___x_2298_ = lean_mk_syntax_ident(v_auxFunName_2034_);
v___x_2299_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2300_ = l_Lean_Syntax_node2(v_a_2296_, v___x_2299_, v___x_2086_, v___x_2087_);
v___x_2301_ = l_Lean_Syntax_node2(v_a_2296_, v___x_2297_, v___x_2298_, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
lean_ctor_set(v___x_2302_, 1, v_a_2085_);
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2089_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2088_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v_a_2064_ = v___x_2304_;
goto v___jp_2063_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
lean_dec(v___x_2087_);
lean_dec(v___x_2086_);
lean_dec(v_a_2085_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2305_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2295_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2295_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
v___jp_2092_:
{
if (v_a_2093_ == 0)
{
uint8_t v___x_2094_; 
v___x_2094_ = lean_unbox(v_snd_2057_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; 
v___x_2095_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc_n(v_a_2096_, 4);
lean_dec_ref(v___x_2095_);
v___x_2097_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_2098_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2099_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2100_, 0, v_a_2096_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = l_Lean_Syntax_node3(v_a_2096_, v___x_2098_, v___x_2086_, v___x_2100_, v___x_2087_);
v___x_2102_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_2103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2103_, 0, v_a_2096_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = l_Lean_Syntax_node3(v_a_2096_, v___x_2097_, v___x_2101_, v___x_2103_, v_fst_2056_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2104_);
v___x_2106_ = v___x_2059_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_snd_2057_);
v___x_2106_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 1, v___x_2106_);
lean_ctor_set(v___x_2054_, 0, v___x_2089_);
v___x_2108_ = v___x_2054_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 1, v___x_2108_);
lean_ctor_set(v___x_2050_, 0, v___x_2088_);
v___x_2110_ = v___x_2050_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
v_a_2064_ = v___x_2110_;
goto v___jp_2063_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
lean_dec(v___x_2087_);
lean_dec(v___x_2086_);
lean_del_object(v___x_2059_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_del_object(v___x_2054_);
lean_del_object(v___x_2050_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2114_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2095_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2095_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v___x_2122_; 
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
v___x_2122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc_n(v_a_2123_, 2);
lean_dec_ref(v___x_2122_);
v___x_2124_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2125_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_a_2123_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = l_Lean_Syntax_node3(v_a_2123_, v___x_2124_, v___x_2086_, v___x_2126_, v___x_2087_);
v___x_2128_ = lean_box(v_a_2093_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2128_);
lean_ctor_set(v___x_2059_, 0, v___x_2127_);
v___x_2130_ = v___x_2059_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2132_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 1, v___x_2130_);
lean_ctor_set(v___x_2054_, 0, v___x_2089_);
v___x_2132_ = v___x_2054_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 1, v___x_2132_);
lean_ctor_set(v___x_2050_, 0, v___x_2088_);
v___x_2134_ = v___x_2050_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
v_a_2064_ = v___x_2134_;
goto v___jp_2063_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
lean_dec(v___x_2087_);
lean_dec(v___x_2086_);
lean_del_object(v___x_2059_);
lean_del_object(v___x_2054_);
lean_del_object(v___x_2050_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2138_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2122_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2122_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
else
{
lean_object* v___x_2146_; 
lean_dec(v_snd_2057_);
v___x_2146_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v_quotContext_2148_; lean_object* v_currMacroScope_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc_n(v_a_2147_, 31);
lean_dec_ref(v___x_2146_);
v_quotContext_2148_ = lean_ctor_get(v___y_2041_, 10);
v_currMacroScope_2149_ = lean_ctor_get(v___y_2041_, 11);
v___x_2150_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11));
v___x_2151_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12));
v___x_2152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2152_, 0, v_a_2147_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14));
v___x_2154_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_2155_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
lean_inc_n(v_currMacroScope_2149_, 4);
lean_inc_n(v_quotContext_2148_, 4);
v___x_2156_ = l_Lean_addMacroScope(v_quotContext_2148_, v___x_2155_, v_currMacroScope_2149_);
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2158_, 0, v_a_2147_);
lean_ctor_set(v___x_2158_, 1, v___x_2154_);
lean_ctor_set(v___x_2158_, 2, v___x_2156_);
lean_ctor_set(v___x_2158_, 3, v___x_2157_);
lean_inc_ref(v___x_2158_);
v___x_2159_ = l_Lean_Syntax_node1(v_a_2147_, v___x_2153_, v___x_2158_);
v___x_2160_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_2161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2161_, 0, v_a_2147_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2163_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_a_2147_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = l_Lean_Syntax_node3(v_a_2147_, v___x_2162_, v___x_2086_, v___x_2164_, v___x_2087_);
v___x_2166_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19));
v___x_2167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2167_, 0, v_a_2147_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21));
v___x_2169_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22));
v___x_2170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2170_, 0, v_a_2147_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25));
v___x_2172_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27));
v___x_2173_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2174_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28));
v___x_2175_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29));
v___x_2176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2176_, 0, v_a_2147_);
lean_ctor_set(v___x_2176_, 1, v___x_2174_);
v___x_2177_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31));
v___x_2178_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2179_, 0, v_a_2147_);
lean_ctor_set(v___x_2179_, 1, v___x_2173_);
lean_ctor_set(v___x_2179_, 2, v___x_2178_);
v___x_2180_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_2181_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2182_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_2183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2183_, 0, v_a_2147_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2185_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_2186_ = lean_box(0);
v___x_2187_ = l_Lean_addMacroScope(v_quotContext_2148_, v___x_2186_, v_currMacroScope_2149_);
v___x_2188_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50));
v___x_2189_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2189_, 0, v_a_2147_);
lean_ctor_set(v___x_2189_, 1, v___x_2185_);
lean_ctor_set(v___x_2189_, 2, v___x_2187_);
lean_ctor_set(v___x_2189_, 3, v___x_2188_);
v___x_2190_ = l_Lean_Syntax_node1(v_a_2147_, v___x_2184_, v___x_2189_);
v___x_2191_ = l_Lean_Syntax_node2(v_a_2147_, v___x_2181_, v___x_2183_, v___x_2190_);
v___x_2192_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2193_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54);
v___x_2194_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55));
v___x_2195_ = l_Lean_addMacroScope(v_quotContext_2148_, v___x_2194_, v_currMacroScope_2149_);
v___x_2196_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59));
v___x_2197_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2197_, 0, v_a_2147_);
lean_ctor_set(v___x_2197_, 1, v___x_2193_);
lean_ctor_set(v___x_2197_, 2, v___x_2195_);
lean_ctor_set(v___x_2197_, 3, v___x_2196_);
v___x_2198_ = l_Lean_Syntax_node1(v_a_2147_, v___x_2173_, v___x_2158_);
v___x_2199_ = l_Lean_Syntax_node2(v_a_2147_, v___x_2192_, v___x_2197_, v___x_2198_);
v___x_2200_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_a_2147_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Lean_Syntax_node3(v_a_2147_, v___x_2180_, v___x_2191_, v___x_2199_, v___x_2201_);
lean_inc_ref_n(v___x_2179_, 3);
v___x_2203_ = l_Lean_Syntax_node2(v_a_2147_, v___x_2177_, v___x_2179_, v___x_2202_);
v___x_2204_ = l_Lean_Syntax_node1(v_a_2147_, v___x_2173_, v___x_2203_);
v___x_2205_ = l_Lean_Syntax_node4(v_a_2147_, v___x_2175_, v___x_2176_, v___x_2204_, v___x_2179_, v___x_2179_);
v___x_2206_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61));
v___x_2207_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62));
v___x_2208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_a_2147_);
lean_ctor_set(v___x_2208_, 1, v___x_2206_);
v___x_2209_ = l_Lean_Syntax_node2(v_a_2147_, v___x_2207_, v___x_2208_, v_fst_2056_);
v___x_2210_ = l_Lean_Syntax_node3(v_a_2147_, v___x_2173_, v___x_2205_, v___x_2179_, v___x_2209_);
v___x_2211_ = l_Lean_Syntax_node1(v_a_2147_, v___x_2172_, v___x_2210_);
v___x_2212_ = l_Lean_Syntax_node1(v_a_2147_, v___x_2171_, v___x_2211_);
v___x_2213_ = l_Lean_Syntax_node2(v_a_2147_, v___x_2168_, v___x_2170_, v___x_2212_);
v___x_2214_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63));
v___x_2215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_a_2147_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_2217_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_2218_ = l_Lean_addMacroScope(v_quotContext_2148_, v___x_2217_, v_currMacroScope_2149_);
v___x_2219_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65));
v___x_2220_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2220_, 0, v_a_2147_);
lean_ctor_set(v___x_2220_, 1, v___x_2216_);
lean_ctor_set(v___x_2220_, 2, v___x_2218_);
lean_ctor_set(v___x_2220_, 3, v___x_2219_);
v___x_2221_ = l_Lean_Syntax_node8(v_a_2147_, v___x_2150_, v___x_2152_, v___x_2159_, v___x_2161_, v___x_2165_, v___x_2167_, v___x_2213_, v___x_2215_, v___x_2220_);
v___x_2222_ = lean_box(v___x_2091_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2222_);
lean_ctor_set(v___x_2059_, 0, v___x_2221_);
v___x_2224_ = v___x_2059_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2226_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 1, v___x_2224_);
lean_ctor_set(v___x_2054_, 0, v___x_2089_);
v___x_2226_ = v___x_2054_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2228_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 1, v___x_2226_);
lean_ctor_set(v___x_2050_, 0, v___x_2088_);
v___x_2228_ = v___x_2050_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
v_a_2064_ = v___x_2228_;
goto v___jp_2063_;
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
lean_dec(v___x_2087_);
lean_dec(v___x_2086_);
lean_del_object(v___x_2059_);
lean_dec(v_fst_2056_);
lean_del_object(v___x_2054_);
lean_del_object(v___x_2050_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2232_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2146_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2146_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
v___jp_2240_:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_nat_dec_lt(v___y_2241_, v___y_2243_);
if (v___x_2244_ == 0)
{
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec(v___x_2072_);
v_a_2093_ = v___x_2091_;
goto v___jp_2092_;
}
else
{
size_t v___x_2245_; size_t v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_usize_of_nat(v___y_2241_);
lean_dec(v___y_2241_);
v___x_2246_ = lean_usize_of_nat(v___y_2243_);
lean_dec(v___y_2243_);
v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_2072_, v___y_2242_, v___x_2245_, v___x_2246_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec_ref(v___y_2242_);
lean_dec(v___x_2072_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; uint8_t v___x_2249_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref(v___x_2247_);
v___x_2249_ = lean_unbox(v_a_2248_);
lean_dec(v_a_2248_);
v_a_2093_ = v___x_2249_;
goto v___jp_2092_;
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
lean_dec(v___x_2087_);
lean_dec(v___x_2086_);
lean_del_object(v___x_2059_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_del_object(v___x_2054_);
lean_del_object(v___x_2050_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2250_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2247_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2247_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
v___jp_2258_:
{
lean_object* v___x_2261_; lean_object* v_array_2262_; lean_object* v_start_2263_; lean_object* v_stop_2264_; uint8_t v___x_2265_; 
lean_inc_ref(v_xs_2031_);
v___x_2261_ = l_Array_toSubarray___redArg(v_xs_2031_, v_lower_2259_, v_upper_2260_);
v_array_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc_ref(v_array_2262_);
v_start_2263_ = lean_ctor_get(v___x_2261_, 1);
lean_inc(v_start_2263_);
v_stop_2264_ = lean_ctor_get(v___x_2261_, 2);
lean_inc(v_stop_2264_);
lean_dec_ref(v___x_2261_);
v___x_2265_ = lean_nat_dec_lt(v_start_2263_, v_stop_2264_);
if (v___x_2265_ == 0)
{
lean_dec(v_stop_2264_);
lean_dec(v_start_2263_);
lean_dec_ref(v_array_2262_);
lean_dec(v___x_2072_);
v_a_2093_ = v___x_2091_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = lean_array_get_size(v_array_2262_);
v___x_2267_ = lean_nat_dec_le(v_stop_2264_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_dec(v_stop_2264_);
v___y_2241_ = v_start_2263_;
v___y_2242_ = v_array_2262_;
v___y_2243_ = v___x_2266_;
goto v___jp_2240_;
}
else
{
v___y_2241_ = v_start_2263_;
v___y_2242_ = v_array_2262_;
v___y_2243_ = v_stop_2264_;
goto v___jp_2240_;
}
}
}
}
else
{
lean_object* v___x_2314_; 
lean_dec(v___x_2087_);
lean_dec(v___x_2086_);
lean_dec(v_a_2085_);
lean_dec(v_a_2083_);
lean_dec(v___x_2072_);
lean_dec(v___x_2069_);
if (v_isShared_2060_ == 0)
{
v___x_2314_ = v___x_2059_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_fst_2056_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_snd_2057_);
v___x_2314_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2316_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 1, v___x_2314_);
lean_ctor_set(v___x_2054_, 0, v___x_2089_);
v___x_2316_ = v___x_2054_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2318_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 1, v___x_2316_);
lean_ctor_set(v___x_2050_, 0, v___x_2088_);
v___x_2318_ = v___x_2050_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
v_a_2064_ = v___x_2318_;
goto v___jp_2063_;
}
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_a_2083_);
lean_dec(v_a_2081_);
lean_dec(v_a_2077_);
lean_dec(v___x_2072_);
lean_dec(v___x_2069_);
lean_del_object(v___x_2059_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_del_object(v___x_2054_);
lean_dec(v_fst_2052_);
lean_del_object(v___x_2050_);
lean_dec(v_fst_2048_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2322_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2084_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2084_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v_a_2081_);
lean_dec(v_a_2077_);
lean_dec(v___x_2072_);
lean_dec(v___x_2069_);
lean_del_object(v___x_2059_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_del_object(v___x_2054_);
lean_dec(v_fst_2052_);
lean_del_object(v___x_2050_);
lean_dec(v_fst_2048_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2330_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2082_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2082_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_a_2077_);
lean_dec(v___x_2072_);
lean_dec(v___x_2069_);
lean_del_object(v___x_2059_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_del_object(v___x_2054_);
lean_dec(v_fst_2052_);
lean_del_object(v___x_2050_);
lean_dec(v_fst_2048_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2338_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2080_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2080_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_a_2075_);
lean_dec(v___x_2072_);
lean_dec(v___x_2069_);
lean_del_object(v___x_2059_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_del_object(v___x_2054_);
lean_dec(v_fst_2052_);
lean_del_object(v___x_2050_);
lean_dec(v_fst_2048_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2346_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2076_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2076_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v___x_2072_);
lean_dec(v___x_2069_);
lean_del_object(v___x_2059_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_del_object(v___x_2054_);
lean_dec(v_fst_2052_);
lean_del_object(v___x_2050_);
lean_dec(v_fst_2048_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2354_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2074_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2074_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v___x_2362_; 
lean_dec(v___x_2072_);
lean_dec(v___x_2069_);
v___x_2362_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc_n(v_a_2363_, 2);
lean_dec_ref(v___x_2362_);
v___x_2364_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_2365_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
v___x_2366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_a_2363_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = l_Lean_Syntax_node1(v_a_2363_, v___x_2364_, v___x_2366_);
v___x_2368_ = lean_array_push(v_fst_2048_, v___x_2367_);
if (v_isShared_2060_ == 0)
{
v___x_2370_ = v___x_2059_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_fst_2056_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_snd_2057_);
v___x_2370_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2372_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 1, v___x_2370_);
v___x_2372_ = v___x_2054_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_fst_2052_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 1, v___x_2372_);
lean_ctor_set(v___x_2050_, 0, v___x_2368_);
v___x_2374_ = v___x_2050_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
v_a_2064_ = v___x_2374_;
goto v___jp_2063_;
}
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_del_object(v___x_2059_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_del_object(v___x_2054_);
lean_dec(v_fst_2052_);
lean_del_object(v___x_2050_);
lean_dec(v_fst_2048_);
lean_dec(v_a_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_xs_2031_);
v_a_2378_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2362_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2362_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
v___jp_2063_:
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_nat_add(v_a_2035_, v___x_2062_);
lean_dec(v_a_2035_);
v_a_2035_ = v___x_2065_;
v_b_2036_ = v_a_2064_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___boxed(lean_object* v_upperBound_2391_, lean_object* v_indVal_2392_, lean_object* v___x_2393_, lean_object* v_xs_2394_, lean_object* v_a_2395_, lean_object* v___x_2396_, lean_object* v_auxFunName_2397_, lean_object* v_a_2398_, lean_object* v_b_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_upperBound_2391_, v_indVal_2392_, v___x_2393_, v_xs_2394_, v_a_2395_, v___x_2396_, v_auxFunName_2397_, v_a_2398_, v_b_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___x_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v___x_2393_);
lean_dec_ref(v_indVal_2392_);
lean_dec(v_upperBound_2391_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1(uint8_t v_rhs__empty_2435_, lean_object* v_numFields_2436_, lean_object* v_indVal_2437_, lean_object* v_name_2438_, lean_object* v_auxFunName_2439_, lean_object* v___f_2440_, lean_object* v_xs_2441_, lean_object* v_type_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_Core_betaReduce(v_type_2442_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v_ref_2452_; lean_object* v_quotContext_2453_; lean_object* v_currMacroScope_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref(v___x_2450_);
v_ref_2452_ = lean_ctor_get(v___y_2447_, 5);
v_quotContext_2453_ = lean_ctor_get(v___y_2447_, 10);
v_currMacroScope_2454_ = lean_ctor_get(v___y_2447_, 11);
v___x_2455_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1);
v___x_2456_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2));
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
v___x_2459_ = 0;
v___x_2460_ = l_Lean_SourceInfo_fromRef(v_ref_2452_, v___x_2459_);
lean_inc(v_currMacroScope_2454_);
lean_inc(v_quotContext_2453_);
v___x_2461_ = l_Lean_addMacroScope(v_quotContext_2453_, v___x_2456_, v_currMacroScope_2454_);
v___x_2462_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5));
v___x_2463_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2460_);
lean_ctor_set(v___x_2463_, 1, v___x_2455_);
lean_ctor_set(v___x_2463_, 2, v___x_2461_);
lean_ctor_set(v___x_2463_, 3, v___x_2462_);
v___x_2464_ = lean_box(v_rhs__empty_2435_);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2458_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2458_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_numFields_2436_, v_indVal_2437_, v_numFields_2436_, v_xs_2441_, v_a_2451_, v_name_2438_, v_auxFunName_2439_, v___x_2457_, v___x_2467_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v_a_2451_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v_snd_2470_; lean_object* v_snd_2471_; lean_object* v_fst_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2570_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref(v___x_2468_);
v_snd_2470_ = lean_ctor_get(v_a_2469_, 1);
lean_inc(v_snd_2470_);
v_snd_2471_ = lean_ctor_get(v_snd_2470_, 1);
lean_inc(v_snd_2471_);
v_fst_2472_ = lean_ctor_get(v_a_2469_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_a_2469_);
if (v_isSharedCheck_2570_ == 0)
{
lean_object* v_unused_2571_; 
v_unused_2571_ = lean_ctor_get(v_a_2469_, 1);
lean_dec(v_unused_2571_);
v___x_2474_ = v_a_2469_;
v_isShared_2475_ = v_isSharedCheck_2570_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_fst_2472_);
lean_dec(v_a_2469_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2570_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v_fst_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2568_; 
v_fst_2476_ = lean_ctor_get(v_snd_2470_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_snd_2470_);
if (v_isSharedCheck_2568_ == 0)
{
lean_object* v_unused_2569_; 
v_unused_2569_ = lean_ctor_get(v_snd_2470_, 1);
lean_dec(v_unused_2569_);
v___x_2478_ = v_snd_2470_;
v_isShared_2479_ = v_isSharedCheck_2568_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_fst_2476_);
lean_dec(v_snd_2470_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2568_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v_fst_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2566_; 
v_fst_2480_ = lean_ctor_get(v_snd_2471_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v_snd_2471_);
if (v_isSharedCheck_2566_ == 0)
{
lean_object* v_unused_2567_; 
v_unused_2567_ = lean_ctor_get(v_snd_2471_, 1);
lean_dec(v_unused_2567_);
v___x_2482_ = v_snd_2471_;
v_isShared_2483_ = v_isSharedCheck_2566_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_fst_2480_);
lean_dec(v_snd_2471_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2566_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v_ctorArgs1_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2535_ = lean_array_get_size(v_fst_2472_);
v___x_2536_ = lean_nat_dec_eq(v___x_2535_, v___x_2457_);
if (v___x_2536_ == 0)
{
v_ctorArgs1_2485_ = v_fst_2472_;
v___y_2486_ = v___y_2443_;
v___y_2487_ = v___y_2444_;
v___y_2488_ = v___y_2445_;
v___y_2489_ = v___y_2446_;
v___y_2490_ = v___y_2447_;
v___y_2491_ = v___y_2448_;
goto v___jp_2484_;
}
else
{
lean_object* v___x_2537_; 
lean_inc_ref(v___f_2440_);
lean_inc(v___y_2448_);
lean_inc_ref(v___y_2447_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
v___x_2537_ = lean_apply_7(v___f_2440_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, lean_box(0));
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc_n(v_a_2538_, 7);
lean_dec_ref(v___x_2537_);
v___x_2539_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5));
v___x_2540_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2541_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_2542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_a_2538_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2544_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_2545_ = lean_box(0);
lean_inc(v_currMacroScope_2454_);
lean_inc(v_quotContext_2453_);
v___x_2546_ = l_Lean_addMacroScope(v_quotContext_2453_, v___x_2545_, v_currMacroScope_2454_);
v___x_2547_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8));
v___x_2548_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2548_, 0, v_a_2538_);
lean_ctor_set(v___x_2548_, 1, v___x_2544_);
lean_ctor_set(v___x_2548_, 2, v___x_2546_);
lean_ctor_set(v___x_2548_, 3, v___x_2547_);
v___x_2549_ = l_Lean_Syntax_node1(v_a_2538_, v___x_2543_, v___x_2548_);
v___x_2550_ = l_Lean_Syntax_node2(v_a_2538_, v___x_2540_, v___x_2542_, v___x_2549_);
v___x_2551_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2552_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2553_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2553_, 0, v_a_2538_);
lean_ctor_set(v___x_2553_, 1, v___x_2551_);
lean_ctor_set(v___x_2553_, 2, v___x_2552_);
v___x_2554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2555_, 0, v_a_2538_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = l_Lean_Syntax_node3(v_a_2538_, v___x_2539_, v___x_2550_, v___x_2553_, v___x_2555_);
v___x_2557_ = lean_array_push(v_fst_2472_, v___x_2556_);
v_ctorArgs1_2485_ = v___x_2557_;
v___y_2486_ = v___y_2443_;
v___y_2487_ = v___y_2444_;
v___y_2488_ = v___y_2445_;
v___y_2489_ = v___y_2446_;
v___y_2490_ = v___y_2447_;
v___y_2491_ = v___y_2448_;
goto v___jp_2484_;
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_del_object(v___x_2482_);
lean_dec(v_fst_2480_);
lean_del_object(v___x_2478_);
lean_dec(v_fst_2476_);
lean_del_object(v___x_2474_);
lean_dec(v_fst_2472_);
lean_dec_ref(v___f_2440_);
v_a_2558_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2537_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2537_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
v___jp_2484_:
{
lean_object* v___x_2492_; 
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc(v___y_2487_);
lean_inc_ref(v___y_2486_);
v___x_2492_ = lean_apply_7(v___f_2440_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, lean_box(0));
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2526_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2526_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2526_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2497_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8));
v___x_2498_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6));
lean_inc(v_a_2493_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set_tag(v___x_2482_, 2);
lean_ctor_set(v___x_2482_, 1, v___x_2498_);
lean_ctor_set(v___x_2482_, 0, v_a_2493_);
v___x_2500_ = v___x_2482_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2493_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0));
v___x_2502_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1));
lean_inc(v_a_2493_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set_tag(v___x_2478_, 2);
lean_ctor_set(v___x_2478_, 1, v___x_2501_);
lean_ctor_set(v___x_2478_, 0, v_a_2493_);
v___x_2504_ = v___x_2478_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2493_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v___x_2501_);
v___x_2504_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3));
v___x_2506_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2507_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2508_ = l_Array_reverse___redArg(v_ctorArgs1_2485_);
v___x_2509_ = l_Array_append___redArg(v___x_2507_, v___x_2508_);
lean_dec_ref(v___x_2508_);
v___x_2510_ = l_Array_reverse___redArg(v_fst_2476_);
v___x_2511_ = l_Array_append___redArg(v___x_2509_, v___x_2510_);
lean_dec_ref(v___x_2510_);
lean_inc_n(v_a_2493_, 3);
v___x_2512_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2512_, 0, v_a_2493_);
lean_ctor_set(v___x_2512_, 1, v___x_2506_);
lean_ctor_set(v___x_2512_, 2, v___x_2511_);
v___x_2513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2513_, 0, v_a_2493_);
lean_ctor_set(v___x_2513_, 1, v___x_2506_);
lean_ctor_set(v___x_2513_, 2, v___x_2507_);
v___x_2514_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 2);
lean_ctor_set(v___x_2474_, 1, v___x_2514_);
lean_ctor_set(v___x_2474_, 0, v_a_2493_);
v___x_2516_ = v___x_2474_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2493_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_inc_n(v_a_2493_, 2);
v___x_2517_ = l_Lean_Syntax_node4(v_a_2493_, v___x_2505_, v___x_2512_, v___x_2513_, v___x_2516_, v_fst_2480_);
v___x_2518_ = l_Lean_Syntax_node2(v_a_2493_, v___x_2502_, v___x_2504_, v___x_2517_);
v___x_2519_ = l_Lean_Syntax_node2(v_a_2493_, v___x_2497_, v___x_2500_, v___x_2518_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2519_);
v___x_2521_ = v___x_2495_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec_ref(v_ctorArgs1_2485_);
lean_del_object(v___x_2482_);
lean_dec(v_fst_2480_);
lean_del_object(v___x_2478_);
lean_dec(v_fst_2476_);
lean_del_object(v___x_2474_);
v_a_2527_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2492_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2492_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref(v___f_2440_);
v_a_2572_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2468_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2468_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec_ref(v_xs_2441_);
lean_dec_ref(v___f_2440_);
lean_dec(v_auxFunName_2439_);
v_a_2580_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2450_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2450_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___boxed(lean_object* v_rhs__empty_2588_, lean_object* v_numFields_2589_, lean_object* v_indVal_2590_, lean_object* v_name_2591_, lean_object* v_auxFunName_2592_, lean_object* v___f_2593_, lean_object* v_xs_2594_, lean_object* v_type_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
uint8_t v_rhs__empty_boxed_2603_; lean_object* v_res_2604_; 
v_rhs__empty_boxed_2603_ = lean_unbox(v_rhs__empty_2588_);
v_res_2604_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1(v_rhs__empty_boxed_2603_, v_numFields_2589_, v_indVal_2590_, v_name_2591_, v_auxFunName_2592_, v___f_2593_, v_xs_2594_, v_type_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v_name_2591_);
lean_dec_ref(v_indVal_2590_);
lean_dec(v_numFields_2589_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0(lean_object* v___x_2605_, lean_object* v_ctors_2606_, uint8_t v_rhs__empty_2607_, lean_object* v_indVal_2608_, lean_object* v_name_2609_, lean_object* v_auxFunName_2610_, lean_object* v___f_2611_, lean_object* v_x_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = l_List_get_x21Internal___redArg(v___x_2605_, v_ctors_2606_, v_x_2612_);
v___x_2621_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v___x_2620_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v_toConstantVal_2623_; lean_object* v_numFields_2624_; lean_object* v_type_2625_; lean_object* v___x_2626_; lean_object* v___f_2627_; uint8_t v___x_2628_; lean_object* v___x_2629_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref(v___x_2621_);
v_toConstantVal_2623_ = lean_ctor_get(v_a_2622_, 0);
lean_inc_ref(v_toConstantVal_2623_);
v_numFields_2624_ = lean_ctor_get(v_a_2622_, 4);
lean_inc(v_numFields_2624_);
lean_dec(v_a_2622_);
v_type_2625_ = lean_ctor_get(v_toConstantVal_2623_, 2);
lean_inc_ref(v_type_2625_);
lean_dec_ref(v_toConstantVal_2623_);
v___x_2626_ = lean_box(v_rhs__empty_2607_);
v___f_2627_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___boxed), 15, 6);
lean_closure_set(v___f_2627_, 0, v___x_2626_);
lean_closure_set(v___f_2627_, 1, v_numFields_2624_);
lean_closure_set(v___f_2627_, 2, v_indVal_2608_);
lean_closure_set(v___f_2627_, 3, v_name_2609_);
lean_closure_set(v___f_2627_, 4, v_auxFunName_2610_);
lean_closure_set(v___f_2627_, 5, v___f_2611_);
v___x_2628_ = 0;
v___x_2629_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_2625_, v___f_2627_, v___x_2628_, v___x_2628_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2629_;
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec_ref(v___f_2611_);
lean_dec(v_auxFunName_2610_);
lean_dec(v_name_2609_);
lean_dec_ref(v_indVal_2608_);
v_a_2630_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2621_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2621_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0___boxed(lean_object* v___x_2638_, lean_object* v_ctors_2639_, lean_object* v_rhs__empty_2640_, lean_object* v_indVal_2641_, lean_object* v_name_2642_, lean_object* v_auxFunName_2643_, lean_object* v___f_2644_, lean_object* v_x_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
uint8_t v_rhs__empty_boxed_2653_; lean_object* v_res_2654_; 
v_rhs__empty_boxed_2653_ = lean_unbox(v_rhs__empty_2640_);
v_res_2654_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0(v___x_2638_, v_ctors_2639_, v_rhs__empty_boxed_2653_, v_indVal_2641_, v_name_2642_, v_auxFunName_2643_, v___f_2644_, v_x_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v_ctors_2639_);
lean_dec(v___x_2638_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(lean_object* v_f_2655_, lean_object* v_n_2656_, lean_object* v_x_2657_, lean_object* v_i_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
uint8_t v___x_2666_; 
v___x_2666_ = lean_nat_dec_lt(v_i_2658_, v_n_2656_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
lean_dec(v_i_2658_);
lean_dec_ref(v_f_2655_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v_x_2657_);
return v___x_2667_;
}
else
{
lean_object* v___x_2668_; 
lean_inc_ref(v_f_2655_);
lean_inc(v___y_2664_);
lean_inc_ref(v___y_2663_);
lean_inc(v___y_2662_);
lean_inc_ref(v___y_2661_);
lean_inc(v___y_2660_);
lean_inc_ref(v___y_2659_);
lean_inc(v_i_2658_);
v___x_2668_ = lean_apply_8(v_f_2655_, v_i_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, lean_box(0));
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2668_);
v___x_2670_ = lean_array_push(v_x_2657_, v_a_2669_);
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_2672_ = lean_nat_add(v_i_2658_, v___x_2671_);
lean_dec(v_i_2658_);
v_x_2657_ = v___x_2670_;
v_i_2658_ = v___x_2672_;
goto _start;
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec(v_i_2658_);
lean_dec_ref(v_x_2657_);
lean_dec_ref(v_f_2655_);
v_a_2674_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2668_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2668_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg___boxed(lean_object* v_f_2682_, lean_object* v_n_2683_, lean_object* v_x_2684_, lean_object* v_i_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_2682_, v_n_2683_, v_x_2684_, v_i_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v_n_2683_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(lean_object* v_n_2694_, lean_object* v_f_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = lean_mk_empty_array_with_capacity(v_n_2694_);
v___x_2704_ = lean_unsigned_to_nat(0u);
v___x_2705_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_2695_, v_n_2694_, v___x_2703_, v___x_2704_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg___boxed(lean_object* v_n_2706_, lean_object* v_f_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v_n_2706_, v_f_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v_n_2706_);
return v_res_2715_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__2));
v___x_2720_ = lean_unsigned_to_nat(2u);
v___x_2721_ = lean_unsigned_to_nat(113u);
v___x_2722_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__1));
v___x_2723_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__0));
v___x_2724_ = l_mkPanicMessageWithDecl(v___x_2723_, v___x_2722_, v___x_2721_, v___x_2720_, v___x_2719_);
return v___x_2724_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8));
v___x_2736_ = l_String_toRawSubstring_x27(v___x_2735_);
return v___x_2736_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16));
v___x_2754_ = l_String_toRawSubstring_x27(v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23));
v___x_2769_ = l_String_toRawSubstring_x27(v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29));
v___x_2783_ = l_String_toRawSubstring_x27(v___x_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(lean_object* v_header_2792_, lean_object* v_indVal_2793_, lean_object* v_auxFunName_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_targetNames_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2995_; 
v_targetNames_2802_ = lean_ctor_get(v_header_2792_, 2);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_header_2792_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; lean_object* v_unused_2997_; lean_object* v_unused_2998_; 
v_unused_2996_ = lean_ctor_get(v_header_2792_, 3);
lean_dec(v_unused_2996_);
v_unused_2997_ = lean_ctor_get(v_header_2792_, 1);
lean_dec(v_unused_2997_);
v_unused_2998_ = lean_ctor_get(v_header_2792_, 0);
lean_dec(v_unused_2998_);
v___x_2804_ = v_header_2792_;
v_isShared_2805_ = v_isSharedCheck_2995_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_targetNames_2802_);
lean_dec(v_header_2792_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2995_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; uint8_t v_rhs__empty_2808_; 
v___x_2806_ = lean_array_get_size(v_targetNames_2802_);
v___x_2807_ = lean_unsigned_to_nat(2u);
v_rhs__empty_2808_ = lean_nat_dec_eq(v___x_2806_, v___x_2807_);
if (v_rhs__empty_2808_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
lean_del_object(v___x_2804_);
lean_dec_ref(v_targetNames_2802_);
lean_dec(v_auxFunName_2794_);
lean_dec_ref(v_indVal_2793_);
v___x_2809_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3);
v___x_2810_ = l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(v___x_2809_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
return v___x_2810_;
}
else
{
lean_object* v_toConstantVal_2811_; lean_object* v_ctors_2812_; lean_object* v_name_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2992_; 
v_toConstantVal_2811_ = lean_ctor_get(v_indVal_2793_, 0);
lean_inc_ref(v_toConstantVal_2811_);
v_ctors_2812_ = lean_ctor_get(v_indVal_2793_, 4);
v_name_2813_ = lean_ctor_get(v_toConstantVal_2811_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_toConstantVal_2811_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; lean_object* v_unused_2994_; 
v_unused_2993_ = lean_ctor_get(v_toConstantVal_2811_, 2);
lean_dec(v_unused_2993_);
v_unused_2994_ = lean_ctor_get(v_toConstantVal_2811_, 1);
lean_dec(v_unused_2994_);
v___x_2815_ = v_toConstantVal_2811_;
v_isShared_2816_ = v_isSharedCheck_2992_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_name_2813_);
lean_dec(v_toConstantVal_2811_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2992_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_ctorIdxName_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_inc_n(v_name_2813_, 2);
v_ctorIdxName_2817_ = l_mkCtorIdxName(v_name_2813_);
v___x_2818_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__5));
v___x_2819_ = l_Lean_Name_append(v_name_2813_, v___x_2818_);
v___x_2820_ = l_Lean_Core_mkFreshUserName(v___x_2819_, v_a_2799_, v_a_2800_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc_n(v_a_2821_, 2);
lean_dec_ref(v___x_2820_);
lean_inc(v_name_2813_);
v___x_2822_ = l_Lean_mkCasesOnSameCtor(v_a_2821_, v_name_2813_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v___f_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___f_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec_ref(v___x_2822_);
v___f_2823_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0));
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_box(v_rhs__empty_2808_);
lean_inc_ref(v_indVal_2793_);
lean_inc(v_ctors_2812_);
v___f_2826_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2826_, 0, v___x_2824_);
lean_closure_set(v___f_2826_, 1, v_ctors_2812_);
lean_closure_set(v___f_2826_, 2, v___x_2825_);
lean_closure_set(v___f_2826_, 3, v_indVal_2793_);
lean_closure_set(v___f_2826_, 4, v_name_2813_);
lean_closure_set(v___f_2826_, 5, v_auxFunName_2794_);
lean_closure_set(v___f_2826_, 6, v___f_2823_);
v___x_2827_ = l_Lean_InductiveVal_numCtors(v_indVal_2793_);
lean_dec_ref(v_indVal_2793_);
v___x_2828_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v___x_2827_, v___f_2826_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2967_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2831_ = v___x_2828_;
v_isShared_2832_ = v_isSharedCheck_2967_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2828_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2967_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v_x1_2836_; lean_object* v___x_2837_; lean_object* v_x2_2838_; uint8_t v___x_2839_; 
v___x_2833_ = lean_unsigned_to_nat(1u);
v___x_2834_ = lean_unsigned_to_nat(0u);
v___x_2835_ = lean_array_get_borrowed(v___x_2824_, v_targetNames_2802_, v___x_2834_);
lean_inc(v___x_2835_);
v_x1_2836_ = lean_mk_syntax_ident(v___x_2835_);
v___x_2837_ = lean_array_get(v___x_2824_, v_targetNames_2802_, v___x_2833_);
lean_dec_ref(v_targetNames_2802_);
v_x2_2838_ = lean_mk_syntax_ident(v___x_2837_);
v___x_2839_ = lean_nat_dec_eq(v___x_2827_, v___x_2833_);
lean_dec(v___x_2827_);
if (v___x_2839_ == 0)
{
lean_object* v_ref_2840_; lean_object* v_quotContext_2841_; lean_object* v_currMacroScope_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v_ref_2840_ = lean_ctor_get(v_a_2799_, 5);
v_quotContext_2841_ = lean_ctor_get(v_a_2799_, 10);
v_currMacroScope_2842_ = lean_ctor_get(v_a_2799_, 11);
v___x_2843_ = l_Lean_SourceInfo_fromRef(v_ref_2840_, v___x_2839_);
v___x_2844_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0));
v___x_2845_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1));
lean_inc_n(v___x_2843_, 2);
v___x_2846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2843_);
lean_ctor_set(v___x_2846_, 1, v___x_2844_);
v___x_2847_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2848_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 1);
lean_ctor_set(v___x_2815_, 2, v___x_2848_);
lean_ctor_set(v___x_2815_, 1, v___x_2847_);
lean_ctor_set(v___x_2815_, 0, v___x_2843_);
v___x_2850_ = v___x_2815_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2942_, 2, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2851_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7));
v___x_2852_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2853_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9);
v___x_2854_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10));
lean_inc(v_currMacroScope_2842_);
lean_inc(v_quotContext_2841_);
v___x_2855_ = l_Lean_addMacroScope(v_quotContext_2841_, v___x_2854_, v_currMacroScope_2842_);
v___x_2856_ = lean_box(0);
v___x_2857_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12));
lean_inc(v___x_2843_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set_tag(v___x_2804_, 3);
lean_ctor_set(v___x_2804_, 3, v___x_2857_);
lean_ctor_set(v___x_2804_, 2, v___x_2855_);
lean_ctor_set(v___x_2804_, 1, v___x_2853_);
lean_ctor_set(v___x_2804_, 0, v___x_2843_);
v___x_2859_ = v___x_2804_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2941_, 2, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2941_, 3, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2860_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_2861_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2862_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
lean_inc_n(v___x_2843_, 41);
v___x_2863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2843_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2865_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
lean_inc_n(v_currMacroScope_2842_, 5);
lean_inc_n(v_quotContext_2841_, 5);
v___x_2866_ = l_Lean_addMacroScope(v_quotContext_2841_, v___x_2824_, v_currMacroScope_2842_);
v___x_2867_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8));
v___x_2868_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2843_);
lean_ctor_set(v___x_2868_, 1, v___x_2865_);
lean_ctor_set(v___x_2868_, 2, v___x_2866_);
lean_ctor_set(v___x_2868_, 3, v___x_2867_);
v___x_2869_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2864_, v___x_2868_);
v___x_2870_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2861_, v___x_2863_, v___x_2869_);
v___x_2871_ = l_Lean_mkCIdent(v_ctorIdxName_2817_);
lean_inc(v_x1_2836_);
v___x_2872_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2847_, v_x1_2836_);
lean_inc(v___x_2871_);
v___x_2873_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2852_, v___x_2871_, v___x_2872_);
v___x_2874_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2843_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
lean_inc_ref(v___x_2875_);
lean_inc(v___x_2870_);
v___x_2876_ = l_Lean_Syntax_node3(v___x_2843_, v___x_2860_, v___x_2870_, v___x_2873_, v___x_2875_);
lean_inc(v_x2_2838_);
v___x_2877_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2847_, v_x2_2838_);
v___x_2878_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2852_, v___x_2871_, v___x_2877_);
v___x_2879_ = l_Lean_Syntax_node3(v___x_2843_, v___x_2860_, v___x_2870_, v___x_2878_, v___x_2875_);
v___x_2880_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2847_, v___x_2876_, v___x_2879_);
v___x_2881_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2852_, v___x_2859_, v___x_2880_);
lean_inc_ref_n(v___x_2850_, 2);
v___x_2882_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2851_, v___x_2850_, v___x_2881_);
v___x_2883_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2847_, v___x_2882_);
v___x_2884_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2));
v___x_2885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2843_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4));
v___x_2887_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_2888_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
v___x_2889_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2843_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14));
v___x_2891_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15));
v___x_2892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2843_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17);
v___x_2894_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18));
v___x_2895_ = l_Lean_addMacroScope(v_quotContext_2841_, v___x_2894_, v_currMacroScope_2842_);
v___x_2896_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22));
v___x_2897_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2843_);
lean_ctor_set(v___x_2897_, 1, v___x_2893_);
lean_ctor_set(v___x_2897_, 2, v___x_2895_);
lean_ctor_set(v___x_2897_, 3, v___x_2896_);
lean_inc_ref(v___x_2892_);
v___x_2898_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2890_, v___x_2892_, v___x_2897_);
v___x_2899_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_2900_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
v___x_2901_ = l_Lean_addMacroScope(v_quotContext_2841_, v___x_2900_, v_currMacroScope_2842_);
v___x_2902_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2843_);
lean_ctor_set(v___x_2902_, 1, v___x_2899_);
lean_ctor_set(v___x_2902_, 2, v___x_2901_);
lean_ctor_set(v___x_2902_, 3, v___x_2856_);
lean_inc_ref(v___x_2902_);
v___x_2903_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2847_, v___x_2902_);
v___x_2904_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2852_, v___x_2898_, v___x_2903_);
v___x_2905_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2847_, v___x_2904_);
v___x_2906_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2847_, v___x_2905_);
v___x_2907_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_2908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2843_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = l_Lean_mkCIdent(v_a_2821_);
v___x_2910_ = l_Array_mkArray3___redArg(v_x1_2836_, v_x2_2838_, v___x_2902_);
v___x_2911_ = l_Array_append___redArg(v___x_2910_, v_a_2829_);
lean_dec(v_a_2829_);
v___x_2912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2843_);
lean_ctor_set(v___x_2912_, 1, v___x_2847_);
lean_ctor_set(v___x_2912_, 2, v___x_2911_);
v___x_2913_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2852_, v___x_2909_, v___x_2912_);
lean_inc_ref(v___x_2908_);
lean_inc_ref(v___x_2889_);
v___x_2914_ = l_Lean_Syntax_node4(v___x_2843_, v___x_2887_, v___x_2889_, v___x_2906_, v___x_2908_, v___x_2913_);
v___x_2915_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24);
v___x_2916_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25));
v___x_2917_ = l_Lean_addMacroScope(v_quotContext_2841_, v___x_2916_, v_currMacroScope_2842_);
v___x_2918_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28));
v___x_2919_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2843_);
lean_ctor_set(v___x_2919_, 1, v___x_2915_);
lean_ctor_set(v___x_2919_, 2, v___x_2917_);
lean_ctor_set(v___x_2919_, 3, v___x_2918_);
v___x_2920_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2890_, v___x_2892_, v___x_2919_);
v___x_2921_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_2922_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
v___x_2923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2843_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2921_, v___x_2923_);
v___x_2925_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2847_, v___x_2924_);
v___x_2926_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2852_, v___x_2920_, v___x_2925_);
v___x_2927_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2847_, v___x_2926_);
v___x_2928_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2847_, v___x_2927_);
v___x_2929_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_2930_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_2931_ = l_Lean_addMacroScope(v_quotContext_2841_, v___x_2930_, v_currMacroScope_2842_);
v___x_2932_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7));
v___x_2933_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2843_);
lean_ctor_set(v___x_2933_, 1, v___x_2929_);
lean_ctor_set(v___x_2933_, 2, v___x_2931_);
lean_ctor_set(v___x_2933_, 3, v___x_2932_);
v___x_2934_ = l_Lean_Syntax_node4(v___x_2843_, v___x_2887_, v___x_2889_, v___x_2928_, v___x_2908_, v___x_2933_);
v___x_2935_ = l_Lean_Syntax_node2(v___x_2843_, v___x_2847_, v___x_2914_, v___x_2934_);
v___x_2936_ = l_Lean_Syntax_node1(v___x_2843_, v___x_2886_, v___x_2935_);
v___x_2937_ = l_Lean_Syntax_node6(v___x_2843_, v___x_2845_, v___x_2846_, v___x_2850_, v___x_2850_, v___x_2883_, v___x_2885_, v___x_2936_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2937_);
v___x_2939_ = v___x_2831_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v_ref_2943_; lean_object* v_quotContext_2944_; lean_object* v_currMacroScope_2945_; uint8_t v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
lean_dec(v_ctorIdxName_2817_);
v_ref_2943_ = lean_ctor_get(v_a_2799_, 5);
v_quotContext_2944_ = lean_ctor_get(v_a_2799_, 10);
v_currMacroScope_2945_ = lean_ctor_get(v_a_2799_, 11);
v___x_2946_ = 0;
v___x_2947_ = l_Lean_SourceInfo_fromRef(v_ref_2943_, v___x_2946_);
v___x_2948_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2949_ = l_Lean_mkCIdent(v_a_2821_);
v___x_2950_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2951_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30);
v___x_2952_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31));
lean_inc(v_currMacroScope_2945_);
lean_inc(v_quotContext_2944_);
v___x_2953_ = l_Lean_addMacroScope(v_quotContext_2944_, v___x_2952_, v_currMacroScope_2945_);
v___x_2954_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33));
lean_inc(v___x_2947_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set_tag(v___x_2804_, 3);
lean_ctor_set(v___x_2804_, 3, v___x_2954_);
lean_ctor_set(v___x_2804_, 2, v___x_2953_);
lean_ctor_set(v___x_2804_, 1, v___x_2951_);
lean_ctor_set(v___x_2804_, 0, v___x_2947_);
v___x_2956_ = v___x_2804_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_2966_, 3, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2957_ = l_Array_mkArray3___redArg(v_x1_2836_, v_x2_2838_, v___x_2956_);
v___x_2958_ = l_Array_append___redArg(v___x_2957_, v_a_2829_);
lean_dec(v_a_2829_);
lean_inc(v___x_2947_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 1);
lean_ctor_set(v___x_2815_, 2, v___x_2958_);
lean_ctor_set(v___x_2815_, 1, v___x_2950_);
lean_ctor_set(v___x_2815_, 0, v___x_2947_);
v___x_2960_ = v___x_2815_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2965_, 2, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2961_ = l_Lean_Syntax_node2(v___x_2947_, v___x_2948_, v___x_2949_, v___x_2960_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2961_);
v___x_2963_ = v___x_2831_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec(v___x_2827_);
lean_dec(v_a_2821_);
lean_dec(v_ctorIdxName_2817_);
lean_del_object(v___x_2815_);
lean_del_object(v___x_2804_);
lean_dec_ref(v_targetNames_2802_);
v_a_2968_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2828_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2828_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_a_2821_);
lean_dec(v_ctorIdxName_2817_);
lean_del_object(v___x_2815_);
lean_dec(v_name_2813_);
lean_del_object(v___x_2804_);
lean_dec_ref(v_targetNames_2802_);
lean_dec(v_auxFunName_2794_);
lean_dec_ref(v_indVal_2793_);
v_a_2976_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2822_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2822_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_ctorIdxName_2817_);
lean_del_object(v___x_2815_);
lean_dec(v_name_2813_);
lean_del_object(v___x_2804_);
lean_dec_ref(v_targetNames_2802_);
lean_dec(v_auxFunName_2794_);
lean_dec_ref(v_indVal_2793_);
v_a_2984_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2820_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2820_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___boxed(lean_object* v_header_2999_, lean_object* v_indVal_3000_, lean_object* v_auxFunName_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(v_header_2999_, v_indVal_3000_, v_auxFunName_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec(v_a_3005_);
lean_dec_ref(v_a_3004_);
lean_dec(v_a_3003_);
lean_dec_ref(v_a_3002_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1(lean_object* v___x_3010_, lean_object* v_as_3011_, size_t v_i_3012_, size_t v_stop_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_3010_, v_as_3011_, v_i_3012_, v_stop_3013_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___boxed(lean_object* v___x_3022_, lean_object* v_as_3023_, lean_object* v_i_3024_, lean_object* v_stop_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
size_t v_i_boxed_3033_; size_t v_stop_boxed_3034_; lean_object* v_res_3035_; 
v_i_boxed_3033_ = lean_unbox_usize(v_i_3024_);
lean_dec(v_i_3024_);
v_stop_boxed_3034_ = lean_unbox_usize(v_stop_3025_);
lean_dec(v_stop_3025_);
v_res_3035_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1(v___x_3022_, v_as_3023_, v_i_boxed_3033_, v_stop_boxed_3034_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v_as_3023_);
lean_dec(v___x_3022_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2(lean_object* v_upperBound_3036_, lean_object* v_indVal_3037_, lean_object* v___x_3038_, lean_object* v_xs_3039_, lean_object* v_a_3040_, lean_object* v___x_3041_, lean_object* v_auxFunName_3042_, lean_object* v_inst_3043_, lean_object* v_R_3044_, lean_object* v_a_3045_, lean_object* v_b_3046_, lean_object* v_c_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_upperBound_3036_, v_indVal_3037_, v___x_3038_, v_xs_3039_, v_a_3040_, v___x_3041_, v_auxFunName_3042_, v_a_3045_, v_b_3046_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_3056_ = _args[0];
lean_object* v_indVal_3057_ = _args[1];
lean_object* v___x_3058_ = _args[2];
lean_object* v_xs_3059_ = _args[3];
lean_object* v_a_3060_ = _args[4];
lean_object* v___x_3061_ = _args[5];
lean_object* v_auxFunName_3062_ = _args[6];
lean_object* v_inst_3063_ = _args[7];
lean_object* v_R_3064_ = _args[8];
lean_object* v_a_3065_ = _args[9];
lean_object* v_b_3066_ = _args[10];
lean_object* v_c_3067_ = _args[11];
lean_object* v___y_3068_ = _args[12];
lean_object* v___y_3069_ = _args[13];
lean_object* v___y_3070_ = _args[14];
lean_object* v___y_3071_ = _args[15];
lean_object* v___y_3072_ = _args[16];
lean_object* v___y_3073_ = _args[17];
lean_object* v___y_3074_ = _args[18];
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2(v_upperBound_3056_, v_indVal_3057_, v___x_3058_, v_xs_3059_, v_a_3060_, v___x_3061_, v_auxFunName_3062_, v_inst_3063_, v_R_3064_, v_a_3065_, v_b_3066_, v_c_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___x_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v___x_3058_);
lean_dec_ref(v_indVal_3057_);
lean_dec(v_upperBound_3056_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3(lean_object* v_00_u03b1_3076_, lean_object* v_n_3077_, lean_object* v_f_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v_n_3077_, v_f_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___boxed(lean_object* v_00_u03b1_3087_, lean_object* v_n_3088_, lean_object* v_f_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3(v_00_u03b1_3087_, v_n_3088_, v_f_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v_n_3088_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3(lean_object* v_00_u03b1_3098_, lean_object* v_f_3099_, lean_object* v_n_3100_, lean_object* v_x_3101_, lean_object* v_i_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_3099_, v_n_3100_, v_x_3101_, v_i_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___boxed(lean_object* v_00_u03b1_3111_, lean_object* v_f_3112_, lean_object* v_n_3113_, lean_object* v_x_3114_, lean_object* v_i_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3(v_00_u03b1_3111_, v_f_3112_, v_n_3113_, v_x_3114_, v_i_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v_n_3113_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(lean_object* v_opts_3124_, lean_object* v_opt_3125_){
_start:
{
lean_object* v_name_3126_; lean_object* v_defValue_3127_; lean_object* v_map_3128_; lean_object* v___x_3129_; 
v_name_3126_ = lean_ctor_get(v_opt_3125_, 0);
v_defValue_3127_ = lean_ctor_get(v_opt_3125_, 1);
v_map_3128_ = lean_ctor_get(v_opts_3124_, 0);
v___x_3129_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3128_, v_name_3126_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_inc(v_defValue_3127_);
return v_defValue_3127_;
}
else
{
lean_object* v_val_3130_; 
v_val_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_val_3130_);
lean_dec_ref(v___x_3129_);
if (lean_obj_tag(v_val_3130_) == 3)
{
lean_object* v_v_3131_; 
v_v_3131_ = lean_ctor_get(v_val_3130_, 0);
lean_inc(v_v_3131_);
lean_dec_ref(v_val_3130_);
return v_v_3131_;
}
else
{
lean_dec(v_val_3130_);
lean_inc(v_defValue_3127_);
return v_defValue_3127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0___boxed(lean_object* v_opts_3132_, lean_object* v_opt_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(v_opts_3132_, v_opt_3133_);
lean_dec_ref(v_opt_3133_);
lean_dec_ref(v_opts_3132_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(lean_object* v_header_3135_, lean_object* v_indVal_3136_, lean_object* v_auxFunName_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v_options_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_options_3145_ = lean_ctor_get(v_a_3142_, 2);
v___x_3146_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_deriving_beq_linear__construction__threshold;
v___x_3147_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(v_options_3145_, v___x_3146_);
v___x_3148_ = l_Lean_InductiveVal_numCtors(v_indVal_3136_);
v___x_3149_ = lean_nat_dec_le(v___x_3147_, v___x_3148_);
lean_dec(v___x_3148_);
lean_dec(v___x_3147_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; 
v___x_3150_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(v_header_3135_, v_indVal_3136_, v_auxFunName_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
return v___x_3150_;
}
else
{
lean_object* v___x_3151_; 
v___x_3151_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(v_header_3135_, v_indVal_3136_, v_auxFunName_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch___boxed(lean_object* v_header_3152_, lean_object* v_indVal_3153_, lean_object* v_auxFunName_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(v_header_3152_, v_indVal_3153_, v_auxFunName_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
return v_res_3162_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4));
v___x_3202_ = l_String_toRawSubstring_x27(v___x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(lean_object* v_ctx_3236_, lean_object* v_i_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v_typeInfos_3245_; lean_object* v_auxFunNames_3246_; uint8_t v_usePartial_3247_; lean_object* v___x_3248_; lean_object* v_indVal_3249_; lean_object* v___x_3250_; 
v_typeInfos_3245_ = lean_ctor_get(v_ctx_3236_, 1);
v_auxFunNames_3246_ = lean_ctor_get(v_ctx_3236_, 2);
v_usePartial_3247_ = lean_ctor_get_uint8(v_ctx_3236_, sizeof(void*)*3);
v___x_3248_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_3249_ = lean_array_get_borrowed(v___x_3248_, v_typeInfos_3245_, v_i_3237_);
lean_inc(v_indVal_3249_);
v___x_3250_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(v_indVal_3249_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3385_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3253_ = v___x_3250_;
v_isShared_3254_ = v_isSharedCheck_3385_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3250_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3385_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v_auxFunName_3256_; lean_object* v_body_3258_; lean_object* v___y_3259_; lean_object* v___x_3368_; 
v___x_3255_ = lean_box(0);
v_auxFunName_3256_ = lean_array_get_borrowed(v___x_3255_, v_auxFunNames_3246_, v_i_3237_);
lean_inc(v_auxFunName_3256_);
lean_inc(v_indVal_3249_);
lean_inc(v_a_3251_);
v___x_3368_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(v_a_3251_, v_indVal_3249_, v_auxFunName_3256_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
if (lean_obj_tag(v___x_3368_) == 0)
{
if (v_usePartial_3247_ == 0)
{
lean_object* v_a_3369_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref(v___x_3368_);
v_body_3258_ = v_a_3369_;
v___y_3259_ = v_a_3242_;
goto v___jp_3257_;
}
else
{
lean_object* v_a_3370_; lean_object* v_argNames_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_a_3370_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3370_);
lean_dec_ref(v___x_3368_);
v_argNames_3371_ = lean_ctor_get(v_a_3251_, 1);
v___x_3372_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
lean_inc_ref(v_argNames_3371_);
v___x_3373_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_3236_, v___x_3372_, v_argNames_3371_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3375_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref(v___x_3373_);
v___x_3375_ = l_Lean_Elab_Deriving_mkLet(v_a_3374_, v_a_3370_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
lean_dec(v_a_3374_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref(v___x_3375_);
v_body_3258_ = v_a_3376_;
v___y_3259_ = v_a_3242_;
goto v___jp_3257_;
}
else
{
lean_del_object(v___x_3253_);
lean_dec(v_a_3251_);
return v___x_3375_;
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec(v_a_3370_);
lean_del_object(v___x_3253_);
lean_dec(v_a_3251_);
v_a_3377_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3373_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3373_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
else
{
lean_del_object(v___x_3253_);
lean_dec(v_a_3251_);
return v___x_3368_;
}
v___jp_3257_:
{
if (v_usePartial_3247_ == 0)
{
lean_object* v_binders_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3307_; 
v_binders_3260_ = lean_ctor_get(v_a_3251_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_a_3251_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; lean_object* v_unused_3309_; lean_object* v_unused_3310_; 
v_unused_3308_ = lean_ctor_get(v_a_3251_, 3);
lean_dec(v_unused_3308_);
v_unused_3309_ = lean_ctor_get(v_a_3251_, 2);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_a_3251_, 1);
lean_dec(v_unused_3310_);
v___x_3262_ = v_a_3251_;
v_isShared_3263_ = v_isSharedCheck_3307_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_binders_3260_);
lean_dec(v_a_3251_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3307_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v_ref_3264_; lean_object* v_quotContext_3265_; lean_object* v_currMacroScope_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3291_; 
v_ref_3264_ = lean_ctor_get(v___y_3259_, 5);
v_quotContext_3265_ = lean_ctor_get(v___y_3259_, 10);
v_currMacroScope_3266_ = lean_ctor_get(v___y_3259_, 11);
v___x_3267_ = l_Lean_SourceInfo_fromRef(v_ref_3264_, v_usePartial_3247_);
v___x_3268_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3269_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3270_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3271_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3267_, 7);
v___x_3272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3267_);
lean_ctor_set(v___x_3272_, 1, v___x_3270_);
lean_ctor_set(v___x_3272_, 2, v___x_3271_);
lean_inc_ref_n(v___x_3272_, 8);
v___x_3273_ = l_Lean_Syntax_node7(v___x_3267_, v___x_3269_, v___x_3272_, v___x_3272_, v___x_3272_, v___x_3272_, v___x_3272_, v___x_3272_, v___x_3272_);
v___x_3274_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3275_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3267_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3256_);
v___x_3278_ = lean_mk_syntax_ident(v_auxFunName_3256_);
v___x_3279_ = l_Lean_Syntax_node2(v___x_3267_, v___x_3277_, v___x_3278_, v___x_3272_);
v___x_3280_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3281_ = l_Array_append___redArg(v___x_3271_, v_binders_3260_);
lean_dec_ref(v_binders_3260_);
v___x_3282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3267_);
lean_ctor_set(v___x_3282_, 1, v___x_3270_);
lean_ctor_set(v___x_3282_, 2, v___x_3281_);
v___x_3283_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3267_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3287_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_3266_);
lean_inc(v_quotContext_3265_);
v___x_3288_ = l_Lean_addMacroScope(v_quotContext_3265_, v___x_3287_, v_currMacroScope_3266_);
v___x_3289_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19));
if (v_isShared_3263_ == 0)
{
lean_ctor_set_tag(v___x_3262_, 3);
lean_ctor_set(v___x_3262_, 3, v___x_3289_);
lean_ctor_set(v___x_3262_, 2, v___x_3288_);
lean_ctor_set(v___x_3262_, 1, v___x_3286_);
lean_ctor_set(v___x_3262_, 0, v___x_3267_);
v___x_3291_ = v___x_3262_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v___x_3286_);
lean_ctor_set(v_reuseFailAlloc_3306_, 2, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3306_, 3, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3304_; 
lean_inc_n(v___x_3267_, 7);
v___x_3292_ = l_Lean_Syntax_node2(v___x_3267_, v___x_3283_, v___x_3285_, v___x_3291_);
v___x_3293_ = l_Lean_Syntax_node1(v___x_3267_, v___x_3270_, v___x_3292_);
v___x_3294_ = l_Lean_Syntax_node2(v___x_3267_, v___x_3280_, v___x_3282_, v___x_3293_);
v___x_3295_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21));
v___x_3296_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3267_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25));
lean_inc_ref_n(v___x_3272_, 3);
v___x_3299_ = l_Lean_Syntax_node2(v___x_3267_, v___x_3298_, v___x_3272_, v___x_3272_);
v___x_3300_ = l_Lean_Syntax_node4(v___x_3267_, v___x_3295_, v___x_3297_, v_body_3258_, v___x_3299_, v___x_3272_);
v___x_3301_ = l_Lean_Syntax_node5(v___x_3267_, v___x_3274_, v___x_3276_, v___x_3279_, v___x_3294_, v___x_3300_, v___x_3272_);
v___x_3302_ = l_Lean_Syntax_node2(v___x_3267_, v___x_3268_, v___x_3273_, v___x_3301_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3302_);
v___x_3304_ = v___x_3253_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
else
{
lean_object* v_binders_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3364_; 
v_binders_3311_ = lean_ctor_get(v_a_3251_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v_a_3251_);
if (v_isSharedCheck_3364_ == 0)
{
lean_object* v_unused_3365_; lean_object* v_unused_3366_; lean_object* v_unused_3367_; 
v_unused_3365_ = lean_ctor_get(v_a_3251_, 3);
lean_dec(v_unused_3365_);
v_unused_3366_ = lean_ctor_get(v_a_3251_, 2);
lean_dec(v_unused_3366_);
v_unused_3367_ = lean_ctor_get(v_a_3251_, 1);
lean_dec(v_unused_3367_);
v___x_3313_ = v_a_3251_;
v_isShared_3314_ = v_isSharedCheck_3364_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_binders_3311_);
lean_dec(v_a_3251_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3364_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v_ref_3315_; lean_object* v_quotContext_3316_; lean_object* v_currMacroScope_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3348_; 
v_ref_3315_ = lean_ctor_get(v___y_3259_, 5);
v_quotContext_3316_ = lean_ctor_get(v___y_3259_, 10);
v_currMacroScope_3317_ = lean_ctor_get(v___y_3259_, 11);
v___x_3318_ = 0;
v___x_3319_ = l_Lean_SourceInfo_fromRef(v_ref_3315_, v___x_3318_);
v___x_3320_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3321_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3322_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3323_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3319_, 10);
v___x_3324_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3319_);
lean_ctor_set(v___x_3324_, 1, v___x_3322_);
lean_ctor_set(v___x_3324_, 2, v___x_3323_);
v___x_3325_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26));
v___x_3326_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27));
v___x_3327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3319_);
lean_ctor_set(v___x_3327_, 1, v___x_3325_);
v___x_3328_ = l_Lean_Syntax_node1(v___x_3319_, v___x_3326_, v___x_3327_);
v___x_3329_ = l_Lean_Syntax_node1(v___x_3319_, v___x_3322_, v___x_3328_);
lean_inc_ref_n(v___x_3324_, 7);
v___x_3330_ = l_Lean_Syntax_node7(v___x_3319_, v___x_3321_, v___x_3324_, v___x_3324_, v___x_3324_, v___x_3324_, v___x_3324_, v___x_3324_, v___x_3329_);
v___x_3331_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3332_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3319_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3256_);
v___x_3335_ = lean_mk_syntax_ident(v_auxFunName_3256_);
v___x_3336_ = l_Lean_Syntax_node2(v___x_3319_, v___x_3334_, v___x_3335_, v___x_3324_);
v___x_3337_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3338_ = l_Array_append___redArg(v___x_3323_, v_binders_3311_);
lean_dec_ref(v_binders_3311_);
v___x_3339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3319_);
lean_ctor_set(v___x_3339_, 1, v___x_3322_);
lean_ctor_set(v___x_3339_, 2, v___x_3338_);
v___x_3340_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3341_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3342_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3319_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3344_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_3317_);
lean_inc(v_quotContext_3316_);
v___x_3345_ = l_Lean_addMacroScope(v_quotContext_3316_, v___x_3344_, v_currMacroScope_3317_);
v___x_3346_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19));
if (v_isShared_3314_ == 0)
{
lean_ctor_set_tag(v___x_3313_, 3);
lean_ctor_set(v___x_3313_, 3, v___x_3346_);
lean_ctor_set(v___x_3313_, 2, v___x_3345_);
lean_ctor_set(v___x_3313_, 1, v___x_3343_);
lean_ctor_set(v___x_3313_, 0, v___x_3319_);
v___x_3348_ = v___x_3313_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3319_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v___x_3345_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3361_; 
lean_inc_n(v___x_3319_, 7);
v___x_3349_ = l_Lean_Syntax_node2(v___x_3319_, v___x_3340_, v___x_3342_, v___x_3348_);
v___x_3350_ = l_Lean_Syntax_node1(v___x_3319_, v___x_3322_, v___x_3349_);
v___x_3351_ = l_Lean_Syntax_node2(v___x_3319_, v___x_3337_, v___x_3339_, v___x_3350_);
v___x_3352_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21));
v___x_3353_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3319_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25));
lean_inc_ref_n(v___x_3324_, 3);
v___x_3356_ = l_Lean_Syntax_node2(v___x_3319_, v___x_3355_, v___x_3324_, v___x_3324_);
v___x_3357_ = l_Lean_Syntax_node4(v___x_3319_, v___x_3352_, v___x_3354_, v_body_3258_, v___x_3356_, v___x_3324_);
v___x_3358_ = l_Lean_Syntax_node5(v___x_3319_, v___x_3331_, v___x_3333_, v___x_3336_, v___x_3351_, v___x_3357_, v___x_3324_);
v___x_3359_ = l_Lean_Syntax_node2(v___x_3319_, v___x_3320_, v___x_3330_, v___x_3358_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3359_);
v___x_3361_ = v___x_3253_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
v_a_3386_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3250_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3250_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___boxed(lean_object* v_ctx_3394_, lean_object* v_i_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(v_ctx_3394_, v_i_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
lean_dec(v_i_3395_);
lean_dec_ref(v_ctx_3394_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_3404_, lean_object* v_ctx_3405_, lean_object* v_a_3406_, lean_object* v_b_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
uint8_t v___x_3415_; 
v___x_3415_ = lean_nat_dec_lt(v_a_3406_, v_upperBound_3404_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; 
lean_dec(v_a_3406_);
v___x_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3416_, 0, v_b_3407_);
return v___x_3416_;
}
else
{
lean_object* v___x_3417_; 
v___x_3417_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(v_ctx_3405_, v_a_3406_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref(v___x_3417_);
v___x_3419_ = lean_array_push(v_b_3407_, v_a_3418_);
v___x_3420_ = lean_unsigned_to_nat(1u);
v___x_3421_ = lean_nat_add(v_a_3406_, v___x_3420_);
lean_dec(v_a_3406_);
v_a_3406_ = v___x_3421_;
v_b_3407_ = v___x_3419_;
goto _start;
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v_b_3407_);
lean_dec(v_a_3406_);
v_a_3423_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3417_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3417_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_3431_, lean_object* v_ctx_3432_, lean_object* v_a_3433_, lean_object* v_b_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v_upperBound_3431_, v_ctx_3432_, v_a_3433_, v_b_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec_ref(v_ctx_3432_);
lean_dec(v_upperBound_3431_);
return v_res_3442_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5(void){
_start:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3456_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__4));
v___x_3457_ = l_String_toRawSubstring_x27(v___x_3456_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(lean_object* v_ctx_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v_typeInfos_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v_auxDefs_3483_; lean_object* v___x_3484_; 
v_typeInfos_3480_ = lean_ctor_get(v_ctx_3472_, 1);
v___x_3481_ = lean_array_get_size(v_typeInfos_3480_);
v___x_3482_ = lean_unsigned_to_nat(0u);
v_auxDefs_3483_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
v___x_3484_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v___x_3481_, v_ctx_3472_, v___x_3482_, v_auxDefs_3483_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3520_; 
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3487_ = v___x_3484_;
v_isShared_3488_ = v_isSharedCheck_3520_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3484_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3520_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v_ref_3489_; lean_object* v_quotContext_3490_; lean_object* v_currMacroScope_3491_; uint8_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3518_; 
v_ref_3489_ = lean_ctor_get(v_a_3477_, 5);
v_quotContext_3490_ = lean_ctor_get(v_a_3477_, 10);
v_currMacroScope_3491_ = lean_ctor_get(v_a_3477_, 11);
v___x_3492_ = 0;
v___x_3493_ = l_Lean_SourceInfo_fromRef(v_ref_3489_, v___x_3492_);
v___x_3494_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0));
v___x_3495_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1));
lean_inc_n(v___x_3493_, 8);
v___x_3496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3493_);
lean_ctor_set(v___x_3496_, 1, v___x_3494_);
v___x_3497_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3498_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2));
v___x_3499_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3));
v___x_3500_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3493_);
lean_ctor_set(v___x_3500_, 1, v___x_3498_);
v___x_3501_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5);
v___x_3502_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7));
lean_inc(v_currMacroScope_3491_);
lean_inc(v_quotContext_3490_);
v___x_3503_ = l_Lean_addMacroScope(v_quotContext_3490_, v___x_3502_, v_currMacroScope_3491_);
v___x_3504_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__10));
v___x_3505_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3493_);
lean_ctor_set(v___x_3505_, 1, v___x_3501_);
lean_ctor_set(v___x_3505_, 2, v___x_3503_);
lean_ctor_set(v___x_3505_, 3, v___x_3504_);
v___x_3506_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_3507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3493_);
lean_ctor_set(v___x_3507_, 1, v___x_3497_);
lean_ctor_set(v___x_3507_, 2, v___x_3506_);
v___x_3508_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0));
v___x_3509_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3493_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
v___x_3510_ = l_Lean_Syntax_node4(v___x_3493_, v___x_3499_, v___x_3500_, v___x_3505_, v___x_3507_, v___x_3509_);
v___x_3511_ = l_Array_mkArray1___redArg(v___x_3510_);
v___x_3512_ = l_Array_append___redArg(v___x_3511_, v_a_3485_);
lean_dec(v_a_3485_);
v___x_3513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3493_);
lean_ctor_set(v___x_3513_, 1, v___x_3497_);
lean_ctor_set(v___x_3513_, 2, v___x_3512_);
v___x_3514_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__11));
v___x_3515_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3493_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
v___x_3516_ = l_Lean_Syntax_node3(v___x_3493_, v___x_3495_, v___x_3496_, v___x_3513_, v___x_3515_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v___x_3516_);
v___x_3518_ = v___x_3487_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
v_a_3521_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3484_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3484_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___boxed(lean_object* v_ctx_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(v_ctx_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec_ref(v_ctx_3529_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0(lean_object* v_upperBound_3538_, lean_object* v_ctx_3539_, lean_object* v_inst_3540_, lean_object* v_R_3541_, lean_object* v_a_3542_, lean_object* v_b_3543_, lean_object* v_c_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v_upperBound_3538_, v_ctx_3539_, v_a_3542_, v_b_3543_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_3553_, lean_object* v_ctx_3554_, lean_object* v_inst_3555_, lean_object* v_R_3556_, lean_object* v_a_3557_, lean_object* v_b_3558_, lean_object* v_c_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0(v_upperBound_3553_, v_ctx_3554_, v_inst_3555_, v_R_3556_, v_a_3557_, v_b_3558_, v_c_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec_ref(v_ctx_3554_);
lean_dec(v_upperBound_3553_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
if (lean_obj_tag(v_a_3568_) == 0)
{
lean_object* v___x_3570_; 
v___x_3570_ = l_List_reverse___redArg(v_a_3569_);
return v___x_3570_;
}
else
{
lean_object* v_head_3571_; lean_object* v_tail_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3581_; 
v_head_3571_ = lean_ctor_get(v_a_3568_, 0);
v_tail_3572_ = lean_ctor_get(v_a_3568_, 1);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_a_3568_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3574_ = v_a_3568_;
v_isShared_3575_ = v_isSharedCheck_3581_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_tail_3572_);
lean_inc(v_head_3571_);
lean_dec(v_a_3568_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3581_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v___x_3578_; 
v___x_3576_ = l_Lean_MessageData_ofSyntax(v_head_3571_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 1, v_a_3569_);
lean_ctor_set(v___x_3574_, 0, v___x_3576_);
v___x_3578_ = v___x_3574_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_a_3569_);
v___x_3578_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
v_a_3568_ = v_tail_3572_;
v_a_3569_ = v___x_3578_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3582_; double v___x_3583_; 
v___x_3582_ = lean_unsigned_to_nat(0u);
v___x_3583_ = lean_float_of_nat(v___x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(lean_object* v_cls_3586_, lean_object* v_msg_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_ref_3593_; lean_object* v___x_3594_; lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3639_; 
v_ref_3593_ = lean_ctor_get(v___y_3590_, 5);
v___x_3594_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3597_ = v___x_3594_;
v_isShared_3598_ = v_isSharedCheck_3639_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3594_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3639_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; lean_object* v_traceState_3600_; lean_object* v_env_3601_; lean_object* v_nextMacroScope_3602_; lean_object* v_ngen_3603_; lean_object* v_auxDeclNGen_3604_; lean_object* v_cache_3605_; lean_object* v_messages_3606_; lean_object* v_infoState_3607_; lean_object* v_snapshotTasks_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3638_; 
v___x_3599_ = lean_st_ref_take(v___y_3591_);
v_traceState_3600_ = lean_ctor_get(v___x_3599_, 4);
v_env_3601_ = lean_ctor_get(v___x_3599_, 0);
v_nextMacroScope_3602_ = lean_ctor_get(v___x_3599_, 1);
v_ngen_3603_ = lean_ctor_get(v___x_3599_, 2);
v_auxDeclNGen_3604_ = lean_ctor_get(v___x_3599_, 3);
v_cache_3605_ = lean_ctor_get(v___x_3599_, 5);
v_messages_3606_ = lean_ctor_get(v___x_3599_, 6);
v_infoState_3607_ = lean_ctor_get(v___x_3599_, 7);
v_snapshotTasks_3608_ = lean_ctor_get(v___x_3599_, 8);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3610_ = v___x_3599_;
v_isShared_3611_ = v_isSharedCheck_3638_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_snapshotTasks_3608_);
lean_inc(v_infoState_3607_);
lean_inc(v_messages_3606_);
lean_inc(v_cache_3605_);
lean_inc(v_traceState_3600_);
lean_inc(v_auxDeclNGen_3604_);
lean_inc(v_ngen_3603_);
lean_inc(v_nextMacroScope_3602_);
lean_inc(v_env_3601_);
lean_dec(v___x_3599_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3638_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
uint64_t v_tid_3612_; lean_object* v_traces_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3637_; 
v_tid_3612_ = lean_ctor_get_uint64(v_traceState_3600_, sizeof(void*)*1);
v_traces_3613_ = lean_ctor_get(v_traceState_3600_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_traceState_3600_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3615_ = v_traceState_3600_;
v_isShared_3616_ = v_isSharedCheck_3637_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_traces_3613_);
lean_dec(v_traceState_3600_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3637_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; double v___x_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3627_; 
v___x_3617_ = lean_box(0);
v___x_3618_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0);
v___x_3619_ = 0;
v___x_3620_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39));
v___x_3621_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3621_, 0, v_cls_3586_);
lean_ctor_set(v___x_3621_, 1, v___x_3617_);
lean_ctor_set(v___x_3621_, 2, v___x_3620_);
lean_ctor_set_float(v___x_3621_, sizeof(void*)*3, v___x_3618_);
lean_ctor_set_float(v___x_3621_, sizeof(void*)*3 + 8, v___x_3618_);
lean_ctor_set_uint8(v___x_3621_, sizeof(void*)*3 + 16, v___x_3619_);
v___x_3622_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__1));
v___x_3623_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3621_);
lean_ctor_set(v___x_3623_, 1, v_a_3595_);
lean_ctor_set(v___x_3623_, 2, v___x_3622_);
lean_inc(v_ref_3593_);
v___x_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3624_, 0, v_ref_3593_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = l_Lean_PersistentArray_push___redArg(v_traces_3613_, v___x_3624_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 0, v___x_3625_);
v___x_3627_ = v___x_3615_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3625_);
lean_ctor_set_uint64(v_reuseFailAlloc_3636_, sizeof(void*)*1, v_tid_3612_);
v___x_3627_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
lean_object* v___x_3629_; 
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 4, v___x_3627_);
v___x_3629_ = v___x_3610_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_env_3601_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_nextMacroScope_3602_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_ngen_3603_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v_auxDeclNGen_3604_);
lean_ctor_set(v_reuseFailAlloc_3635_, 4, v___x_3627_);
lean_ctor_set(v_reuseFailAlloc_3635_, 5, v_cache_3605_);
lean_ctor_set(v_reuseFailAlloc_3635_, 6, v_messages_3606_);
lean_ctor_set(v_reuseFailAlloc_3635_, 7, v_infoState_3607_);
lean_ctor_set(v_reuseFailAlloc_3635_, 8, v_snapshotTasks_3608_);
v___x_3629_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; 
v___x_3630_ = lean_st_ref_set(v___y_3591_, v___x_3629_);
v___x_3631_ = lean_box(0);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v___x_3631_);
v___x_3633_ = v___x_3597_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_3640_, lean_object* v_msg_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v_cls_3640_, v_msg_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
return v_res_3647_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3656_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__2));
v___x_3657_ = l_Lean_Name_append(v___x_3656_, v___x_3655_);
return v___x_3657_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__4));
v___x_3660_ = l_Lean_stringToMessageData(v___x_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(lean_object* v_ctx_3661_, lean_object* v_declName_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(v_ctx_3661_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; lean_object* v___x_3677_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref(v___x_3670_);
v___x_3672_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_3673_ = lean_unsigned_to_nat(1u);
v___x_3674_ = lean_mk_empty_array_with_capacity(v___x_3673_);
lean_inc_ref(v___x_3674_);
v___x_3675_ = lean_array_push(v___x_3674_, v_declName_3662_);
v___x_3676_ = 1;
v___x_3677_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_3661_, v___x_3672_, v___x_3675_, v___x_3676_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_);
lean_dec_ref(v___x_3675_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_options_3678_; lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3719_; 
v_options_3678_ = lean_ctor_get(v_a_3667_, 2);
v_a_3679_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3681_ = v___x_3677_;
v_isShared_3682_ = v_isSharedCheck_3719_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3677_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3719_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v_inheritedTraceOptions_3683_; uint8_t v_hasTrace_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v_inheritedTraceOptions_3683_ = lean_ctor_get(v_a_3667_, 13);
v_hasTrace_3684_ = lean_ctor_get_uint8(v_options_3678_, sizeof(void*)*1);
v___x_3685_ = lean_array_push(v___x_3674_, v_a_3671_);
v___x_3686_ = l_Array_append___redArg(v___x_3685_, v_a_3679_);
lean_dec(v_a_3679_);
if (v_hasTrace_3684_ == 0)
{
lean_object* v___x_3688_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v___x_3686_);
v___x_3688_ = v___x_3681_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; uint8_t v___x_3692_; 
v___x_3690_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3691_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3);
v___x_3692_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3683_, v_options_3678_, v___x_3691_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3694_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v___x_3686_);
v___x_3694_ = v___x_3681_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3686_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_del_object(v___x_3681_);
v___x_3696_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5);
lean_inc_ref(v___x_3686_);
v___x_3697_ = lean_array_to_list(v___x_3686_);
v___x_3698_ = lean_box(0);
v___x_3699_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(v___x_3697_, v___x_3698_);
v___x_3700_ = l_Lean_MessageData_ofList(v___x_3699_);
v___x_3701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3696_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v___x_3690_, v___x_3701_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v___x_3702_, 0);
lean_dec(v_unused_3710_);
v___x_3704_ = v___x_3702_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_dec(v___x_3702_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3686_);
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3686_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec_ref(v___x_3686_);
v_a_3711_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3702_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3702_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec_ref(v___x_3674_);
lean_dec(v_a_3671_);
v_a_3720_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3677_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3677_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec(v_declName_3662_);
lean_dec_ref(v_ctx_3661_);
v_a_3728_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3670_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3670_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___boxed(lean_object* v_ctx_3736_, lean_object* v_declName_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(v_ctx_3736_, v_declName_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
lean_dec(v_a_3743_);
lean_dec_ref(v_a_3742_);
lean_dec(v_a_3741_);
lean_dec_ref(v_a_3740_);
lean_dec(v_a_3739_);
lean_dec_ref(v_a_3738_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1(lean_object* v_cls_3746_, lean_object* v_msg_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v_cls_3746_, v_msg_3747_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___boxed(lean_object* v_cls_3756_, lean_object* v_msg_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1(v_cls_3756_, v_msg_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
return v_res_3765_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2));
v___x_3774_ = l_String_toRawSubstring_x27(v___x_3773_);
return v___x_3774_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5));
v___x_3779_ = l_String_toRawSubstring_x27(v___x_3778_);
return v___x_3779_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3792_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__11));
v___x_3793_ = l_String_toRawSubstring_x27(v___x_3792_);
return v___x_3793_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16(void){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__15));
v___x_3800_ = l_String_toRawSubstring_x27(v___x_3799_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(lean_object* v_ctx_3804_, lean_object* v_name_3805_, lean_object* v_a_3806_){
_start:
{
lean_object* v_auxFunNames_3808_; lean_object* v_ref_3809_; lean_object* v_quotContext_3810_; lean_object* v_currMacroScope_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v_auxFunName_3814_; uint8_t v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v_auxFunNames_3808_ = lean_ctor_get(v_ctx_3804_, 2);
v_ref_3809_ = lean_ctor_get(v_a_3806_, 5);
v_quotContext_3810_ = lean_ctor_get(v_a_3806_, 10);
v_currMacroScope_3811_ = lean_ctor_get(v_a_3806_, 11);
v___x_3812_ = lean_box(0);
v___x_3813_ = lean_unsigned_to_nat(0u);
v_auxFunName_3814_ = lean_array_get_borrowed(v___x_3812_, v_auxFunNames_3808_, v___x_3813_);
v___x_3815_ = 0;
v___x_3816_ = l_Lean_SourceInfo_fromRef(v_ref_3809_, v___x_3815_);
v___x_3817_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3818_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3819_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3820_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3816_, 25);
v___x_3821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3816_);
lean_ctor_set(v___x_3821_, 1, v___x_3819_);
lean_ctor_set(v___x_3821_, 2, v___x_3820_);
lean_inc_ref_n(v___x_3821_, 12);
v___x_3822_ = l_Lean_Syntax_node7(v___x_3816_, v___x_3818_, v___x_3821_, v___x_3821_, v___x_3821_, v___x_3821_, v___x_3821_, v___x_3821_, v___x_3821_);
v___x_3823_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3824_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3816_);
lean_ctor_set(v___x_3825_, 1, v___x_3824_);
v___x_3826_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3814_);
v___x_3827_ = lean_mk_syntax_ident(v_auxFunName_3814_);
v___x_3828_ = l_Lean_Syntax_node2(v___x_3816_, v___x_3826_, v___x_3827_, v___x_3821_);
v___x_3829_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3830_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1));
v___x_3831_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_3832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3816_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
v___x_3833_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3);
v___x_3834_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__4));
lean_inc_n(v_currMacroScope_3811_, 5);
lean_inc_n(v_quotContext_3810_, 5);
v___x_3835_ = l_Lean_addMacroScope(v_quotContext_3810_, v___x_3834_, v_currMacroScope_3811_);
v___x_3836_ = lean_box(0);
v___x_3837_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3816_);
lean_ctor_set(v___x_3837_, 1, v___x_3833_);
lean_ctor_set(v___x_3837_, 2, v___x_3835_);
lean_ctor_set(v___x_3837_, 3, v___x_3836_);
v___x_3838_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6);
v___x_3839_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__7));
v___x_3840_ = l_Lean_addMacroScope(v_quotContext_3810_, v___x_3839_, v_currMacroScope_3811_);
v___x_3841_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3816_);
lean_ctor_set(v___x_3841_, 1, v___x_3838_);
lean_ctor_set(v___x_3841_, 2, v___x_3840_);
lean_ctor_set(v___x_3841_, 3, v___x_3836_);
v___x_3842_ = l_Lean_Syntax_node2(v___x_3816_, v___x_3819_, v___x_3837_, v___x_3841_);
v___x_3843_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3816_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = l_Lean_mkCIdent(v_name_3805_);
lean_inc_ref(v___x_3844_);
v___x_3846_ = l_Lean_Syntax_node2(v___x_3816_, v___x_3819_, v___x_3844_, v___x_3845_);
v___x_3847_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_3848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3816_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = l_Lean_Syntax_node5(v___x_3816_, v___x_3830_, v___x_3832_, v___x_3842_, v___x_3846_, v___x_3821_, v___x_3848_);
v___x_3850_ = l_Lean_Syntax_node1(v___x_3816_, v___x_3819_, v___x_3849_);
v___x_3851_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3852_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3853_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
v___x_3854_ = l_Lean_addMacroScope(v_quotContext_3810_, v___x_3853_, v_currMacroScope_3811_);
v___x_3855_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__10));
v___x_3856_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3816_);
lean_ctor_set(v___x_3856_, 1, v___x_3852_);
lean_ctor_set(v___x_3856_, 2, v___x_3854_);
lean_ctor_set(v___x_3856_, 3, v___x_3855_);
v___x_3857_ = l_Lean_Syntax_node2(v___x_3816_, v___x_3851_, v___x_3844_, v___x_3856_);
v___x_3858_ = l_Lean_Syntax_node1(v___x_3816_, v___x_3819_, v___x_3857_);
v___x_3859_ = l_Lean_Syntax_node2(v___x_3816_, v___x_3829_, v___x_3850_, v___x_3858_);
v___x_3860_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21));
v___x_3861_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3816_);
lean_ctor_set(v___x_3862_, 1, v___x_3861_);
v___x_3863_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_3864_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12);
v___x_3865_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14));
v___x_3866_ = l_Lean_addMacroScope(v_quotContext_3810_, v___x_3865_, v_currMacroScope_3811_);
v___x_3867_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3816_);
lean_ctor_set(v___x_3867_, 1, v___x_3864_);
lean_ctor_set(v___x_3867_, 2, v___x_3866_);
lean_ctor_set(v___x_3867_, 3, v___x_3836_);
v___x_3868_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_3869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3816_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16);
v___x_3871_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17));
v___x_3872_ = l_Lean_addMacroScope(v_quotContext_3810_, v___x_3871_, v_currMacroScope_3811_);
v___x_3873_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3816_);
lean_ctor_set(v___x_3873_, 1, v___x_3870_);
lean_ctor_set(v___x_3873_, 2, v___x_3872_);
lean_ctor_set(v___x_3873_, 3, v___x_3836_);
v___x_3874_ = l_Lean_Syntax_node3(v___x_3816_, v___x_3863_, v___x_3867_, v___x_3869_, v___x_3873_);
v___x_3875_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25));
v___x_3876_ = l_Lean_Syntax_node2(v___x_3816_, v___x_3875_, v___x_3821_, v___x_3821_);
v___x_3877_ = l_Lean_Syntax_node4(v___x_3816_, v___x_3860_, v___x_3862_, v___x_3874_, v___x_3876_, v___x_3821_);
v___x_3878_ = l_Lean_Syntax_node5(v___x_3816_, v___x_3823_, v___x_3825_, v___x_3828_, v___x_3859_, v___x_3877_, v___x_3821_);
v___x_3879_ = l_Lean_Syntax_node2(v___x_3816_, v___x_3817_, v___x_3822_, v___x_3878_);
v___x_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___boxed(lean_object* v_ctx_3881_, lean_object* v_name_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3881_, v_name_3882_, v_a_3883_);
lean_dec_ref(v_a_3883_);
lean_dec_ref(v_ctx_3881_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun(lean_object* v_ctx_3886_, lean_object* v_name_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3886_, v_name_3887_, v_a_3892_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___boxed(lean_object* v_ctx_3896_, lean_object* v_name_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun(v_ctx_3896_, v_name_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
lean_dec(v_a_3901_);
lean_dec_ref(v_a_3900_);
lean_dec(v_a_3899_);
lean_dec_ref(v_a_3898_);
lean_dec_ref(v_ctx_3896_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(lean_object* v_ctx_3906_, lean_object* v_name_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v___x_3915_; lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; lean_object* v___x_3922_; 
lean_inc(v_name_3907_);
v___x_3915_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3906_, v_name_3907_, v_a_3912_);
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref(v___x_3915_);
v___x_3917_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_3918_ = lean_unsigned_to_nat(1u);
v___x_3919_ = lean_mk_empty_array_with_capacity(v___x_3918_);
lean_inc_ref(v___x_3919_);
v___x_3920_ = lean_array_push(v___x_3919_, v_name_3907_);
v___x_3921_ = 1;
v___x_3922_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_3906_, v___x_3917_, v___x_3920_, v___x_3921_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec_ref(v___x_3920_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_options_3923_; lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3964_; 
v_options_3923_ = lean_ctor_get(v_a_3912_, 2);
v_a_3924_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3926_ = v___x_3922_;
v_isShared_3927_ = v_isSharedCheck_3964_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3922_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3964_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v_inheritedTraceOptions_3928_; uint8_t v_hasTrace_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_inheritedTraceOptions_3928_ = lean_ctor_get(v_a_3912_, 13);
v_hasTrace_3929_ = lean_ctor_get_uint8(v_options_3923_, sizeof(void*)*1);
v___x_3930_ = lean_array_push(v___x_3919_, v_a_3916_);
v___x_3931_ = l_Array_append___redArg(v___x_3930_, v_a_3924_);
lean_dec(v_a_3924_);
if (v_hasTrace_3929_ == 0)
{
lean_object* v___x_3933_; 
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v___x_3931_);
v___x_3933_ = v___x_3926_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3931_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
else
{
lean_object* v___x_3935_; lean_object* v___x_3936_; uint8_t v___x_3937_; 
v___x_3935_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3936_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3);
v___x_3937_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3928_, v_options_3923_, v___x_3936_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3939_; 
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v___x_3931_);
v___x_3939_ = v___x_3926_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3931_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
lean_del_object(v___x_3926_);
v___x_3941_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5);
lean_inc_ref(v___x_3931_);
v___x_3942_ = lean_array_to_list(v___x_3931_);
v___x_3943_ = lean_box(0);
v___x_3944_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(v___x_3942_, v___x_3943_);
v___x_3945_ = l_Lean_MessageData_ofList(v___x_3944_);
v___x_3946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3941_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
v___x_3947_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v___x_3935_, v___x_3946_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3954_ == 0)
{
lean_object* v_unused_3955_; 
v_unused_3955_ = lean_ctor_get(v___x_3947_, 0);
lean_dec(v_unused_3955_);
v___x_3949_ = v___x_3947_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_dec(v___x_3947_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 0, v___x_3931_);
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3931_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec_ref(v___x_3931_);
v_a_3956_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3947_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3947_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec_ref(v___x_3919_);
lean_dec(v_a_3916_);
v_a_3965_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3922_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3922_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd___boxed(lean_object* v_ctx_3973_, lean_object* v_name_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(v_ctx_3973_, v_name_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(lean_object* v___y_3983_){
_start:
{
lean_object* v___x_3985_; lean_object* v_env_3986_; lean_object* v___x_3987_; lean_object* v_mainModule_3988_; lean_object* v___x_3989_; 
v___x_3985_ = lean_st_ref_get(v___y_3983_);
v_env_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc_ref(v_env_3986_);
lean_dec(v___x_3985_);
v___x_3987_ = l_Lean_Environment_header(v_env_3986_);
lean_dec_ref(v_env_3986_);
v_mainModule_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_mainModule_3988_);
lean_dec_ref(v___x_3987_);
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v_mainModule_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg___boxed(lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_3990_);
lean_dec(v___y_3990_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0(lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_3994_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___boxed(lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0(v___y_3997_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0(uint8_t v_a_4001_, lean_object* v_a_4002_, lean_object* v_declName_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
if (v_a_4001_ == 0)
{
lean_object* v___x_4011_; 
v___x_4011_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(v_a_4002_, v_declName_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
return v___x_4011_;
}
else
{
lean_object* v___x_4012_; 
v___x_4012_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(v_a_4002_, v_declName_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
return v___x_4012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0___boxed(lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_declName_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
uint8_t v_a_6400__boxed_4023_; lean_object* v_res_4024_; 
v_a_6400__boxed_4023_ = lean_unbox(v_a_4013_);
v_res_4024_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0(v_a_6400__boxed_4023_, v_a_4014_, v_declName_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
return v_res_4024_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4025_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4026_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
return v___x_4027_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_4029_ = lean_unsigned_to_nat(0u);
v___x_4030_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
lean_ctor_set(v___x_4030_, 1, v___x_4029_);
lean_ctor_set(v___x_4030_, 2, v___x_4029_);
lean_ctor_set(v___x_4030_, 3, v___x_4029_);
lean_ctor_set(v___x_4030_, 4, v___x_4028_);
lean_ctor_set(v___x_4030_, 5, v___x_4028_);
lean_ctor_set(v___x_4030_, 6, v___x_4028_);
lean_ctor_set(v___x_4030_, 7, v___x_4028_);
lean_ctor_set(v___x_4030_, 8, v___x_4028_);
lean_ctor_set(v___x_4030_, 9, v___x_4028_);
return v___x_4030_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4031_ = lean_unsigned_to_nat(32u);
v___x_4032_ = lean_mk_empty_array_with_capacity(v___x_4031_);
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
return v___x_4033_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4034_ = ((size_t)5ULL);
v___x_4035_ = lean_unsigned_to_nat(0u);
v___x_4036_ = lean_unsigned_to_nat(32u);
v___x_4037_ = lean_mk_empty_array_with_capacity(v___x_4036_);
v___x_4038_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_4039_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
lean_ctor_set(v___x_4039_, 1, v___x_4037_);
lean_ctor_set(v___x_4039_, 2, v___x_4035_);
lean_ctor_set(v___x_4039_, 3, v___x_4035_);
lean_ctor_set_usize(v___x_4039_, 4, v___x_4034_);
return v___x_4039_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4040_ = lean_box(1);
v___x_4041_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_4042_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_4043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
lean_ctor_set(v___x_4043_, 1, v___x_4041_);
lean_ctor_set(v___x_4043_, 2, v___x_4040_);
return v___x_4043_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_4046_ = l_Lean_stringToMessageData(v___x_4045_);
return v___x_4046_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_4049_ = l_Lean_stringToMessageData(v___x_4048_);
return v___x_4049_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4051_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_4052_ = l_Lean_stringToMessageData(v___x_4051_);
return v___x_4052_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_4055_ = l_Lean_stringToMessageData(v___x_4054_);
return v___x_4055_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_4058_ = l_Lean_stringToMessageData(v___x_4057_);
return v___x_4058_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_4061_ = l_Lean_stringToMessageData(v___x_4060_);
return v___x_4061_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_4064_ = l_Lean_stringToMessageData(v___x_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_4065_, lean_object* v_declHint_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v___x_4069_; lean_object* v_env_4070_; uint8_t v___x_4071_; 
v___x_4069_ = lean_st_ref_get(v___y_4067_);
v_env_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc_ref(v_env_4070_);
lean_dec(v___x_4069_);
v___x_4071_ = l_Lean_Name_isAnonymous(v_declHint_4066_);
if (v___x_4071_ == 0)
{
uint8_t v_isExporting_4072_; 
v_isExporting_4072_ = lean_ctor_get_uint8(v_env_4070_, sizeof(void*)*8);
if (v_isExporting_4072_ == 0)
{
lean_object* v___x_4073_; 
lean_dec_ref(v_env_4070_);
lean_dec(v_declHint_4066_);
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v_msg_4065_);
return v___x_4073_;
}
else
{
lean_object* v___x_4074_; uint8_t v___x_4075_; 
lean_inc_ref(v_env_4070_);
v___x_4074_ = l_Lean_Environment_setExporting(v_env_4070_, v___x_4071_);
lean_inc(v_declHint_4066_);
lean_inc_ref(v___x_4074_);
v___x_4075_ = l_Lean_Environment_contains(v___x_4074_, v_declHint_4066_, v_isExporting_4072_);
if (v___x_4075_ == 0)
{
lean_object* v___x_4076_; 
lean_dec_ref(v___x_4074_);
lean_dec_ref(v_env_4070_);
lean_dec(v_declHint_4066_);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v_msg_4065_);
return v___x_4076_;
}
else
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v_c_4082_; lean_object* v___x_4083_; 
v___x_4077_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_4078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_4079_ = l_Lean_Options_empty;
v___x_4080_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4074_);
lean_ctor_set(v___x_4080_, 1, v___x_4077_);
lean_ctor_set(v___x_4080_, 2, v___x_4078_);
lean_ctor_set(v___x_4080_, 3, v___x_4079_);
lean_inc(v_declHint_4066_);
v___x_4081_ = l_Lean_MessageData_ofConstName(v_declHint_4066_, v___x_4071_);
v_c_4082_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4082_, 0, v___x_4080_);
lean_ctor_set(v_c_4082_, 1, v___x_4081_);
v___x_4083_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4070_, v_declHint_4066_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
lean_dec_ref(v_env_4070_);
lean_dec(v_declHint_4066_);
v___x_4084_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_4085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
lean_ctor_set(v___x_4085_, 1, v_c_4082_);
v___x_4086_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_4087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4085_);
lean_ctor_set(v___x_4087_, 1, v___x_4086_);
v___x_4088_ = l_Lean_MessageData_note(v___x_4087_);
v___x_4089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4089_, 0, v_msg_4065_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
return v___x_4090_;
}
else
{
lean_object* v_val_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4126_; 
v_val_4091_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4093_ = v___x_4083_;
v_isShared_4094_ = v_isSharedCheck_4126_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_val_4091_);
lean_dec(v___x_4083_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4126_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v_mod_4098_; uint8_t v___x_4099_; 
v___x_4095_ = lean_box(0);
v___x_4096_ = l_Lean_Environment_header(v_env_4070_);
lean_dec_ref(v_env_4070_);
v___x_4097_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4096_);
v_mod_4098_ = lean_array_get(v___x_4095_, v___x_4097_, v_val_4091_);
lean_dec(v_val_4091_);
lean_dec_ref(v___x_4097_);
v___x_4099_ = l_Lean_isPrivateName(v_declHint_4066_);
lean_dec(v_declHint_4066_);
if (v___x_4099_ == 0)
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4111_; 
v___x_4100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_4101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4100_);
lean_ctor_set(v___x_4101_, 1, v_c_4082_);
v___x_4102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_4103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4101_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
v___x_4104_ = l_Lean_MessageData_ofName(v_mod_4098_);
v___x_4105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4103_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
v___x_4106_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_4107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4105_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = l_Lean_MessageData_note(v___x_4107_);
v___x_4109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4109_, 0, v_msg_4065_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set_tag(v___x_4093_, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4109_);
v___x_4111_ = v___x_4093_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4109_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
else
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4124_; 
v___x_4113_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_4114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
lean_ctor_set(v___x_4114_, 1, v_c_4082_);
v___x_4115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_4116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4114_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
v___x_4117_ = l_Lean_MessageData_ofName(v_mod_4098_);
v___x_4118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4116_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
v___x_4119_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_4120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4118_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = l_Lean_MessageData_note(v___x_4120_);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v_msg_4065_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set_tag(v___x_4093_, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4122_);
v___x_4124_ = v___x_4093_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4122_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4127_; 
lean_dec_ref(v_env_4070_);
lean_dec(v_declHint_4066_);
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v_msg_4065_);
return v___x_4127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_4128_, lean_object* v_declHint_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4128_, v_declHint_4129_, v___y_4130_);
lean_dec(v___y_4130_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_4133_, lean_object* v_declHint_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v___x_4138_; lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4148_; 
v___x_4138_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4133_, v_declHint_4134_, v___y_4136_);
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4141_ = v___x_4138_;
v_isShared_4142_ = v_isSharedCheck_4148_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4138_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4148_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4146_; 
v___x_4143_ = l_Lean_unknownIdentifierMessageTag;
v___x_4144_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
lean_ctor_set(v___x_4144_, 1, v_a_4139_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v___x_4144_);
v___x_4146_ = v___x_4141_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4144_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_4149_, lean_object* v_declHint_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_4149_, v_declHint_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(lean_object* v_msgData_4155_, lean_object* v_macroStack_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v___x_4159_; lean_object* v_scopes_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v_opts_4163_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
v___x_4159_ = lean_st_ref_get(v___y_4157_);
v_scopes_4160_ = lean_ctor_get(v___x_4159_, 2);
lean_inc(v_scopes_4160_);
lean_dec(v___x_4159_);
v___x_4161_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4162_ = l_List_head_x21___redArg(v___x_4161_, v_scopes_4160_);
lean_dec(v_scopes_4160_);
v_opts_4163_ = lean_ctor_get(v___x_4162_, 1);
lean_inc_ref(v_opts_4163_);
lean_dec(v___x_4162_);
v___x_4164_ = l_Lean_Elab_pp_macroStack;
v___x_4165_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v_opts_4163_, v___x_4164_);
lean_dec_ref(v_opts_4163_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; 
lean_dec(v_macroStack_4156_);
v___x_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4166_, 0, v_msgData_4155_);
return v___x_4166_;
}
else
{
if (lean_obj_tag(v_macroStack_4156_) == 0)
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v_msgData_4155_);
return v___x_4167_;
}
else
{
lean_object* v_head_4168_; lean_object* v_after_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4184_; 
v_head_4168_ = lean_ctor_get(v_macroStack_4156_, 0);
lean_inc(v_head_4168_);
v_after_4169_ = lean_ctor_get(v_head_4168_, 1);
v_isSharedCheck_4184_ = !lean_is_exclusive(v_head_4168_);
if (v_isSharedCheck_4184_ == 0)
{
lean_object* v_unused_4185_; 
v_unused_4185_ = lean_ctor_get(v_head_4168_, 0);
lean_dec(v_unused_4185_);
v___x_4171_ = v_head_4168_;
v_isShared_4172_ = v_isSharedCheck_4184_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_after_4169_);
lean_dec(v_head_4168_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4184_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4173_; lean_object* v___x_4175_; 
v___x_4173_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_4172_ == 0)
{
lean_ctor_set_tag(v___x_4171_, 7);
lean_ctor_set(v___x_4171_, 1, v___x_4173_);
lean_ctor_set(v___x_4171_, 0, v_msgData_4155_);
v___x_4175_ = v___x_4171_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_msgData_4155_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v_msgData_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4176_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_4177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4175_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
v___x_4178_ = l_Lean_MessageData_ofSyntax(v_after_4169_);
v___x_4179_ = l_Lean_indentD(v___x_4178_);
v_msgData_4180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4180_, 0, v___x_4177_);
lean_ctor_set(v_msgData_4180_, 1, v___x_4179_);
v___x_4181_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_msgData_4180_, v_macroStack_4156_);
v___x_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
return v___x_4182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_msgData_4186_, lean_object* v_macroStack_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_msgData_4186_, v_macroStack_4187_, v___y_4188_);
lean_dec(v___y_4188_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(lean_object* v_msgData_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v___x_4194_; lean_object* v_env_4195_; lean_object* v___x_4196_; lean_object* v_scopes_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v_opts_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4194_ = lean_st_ref_get(v___y_4192_);
v_env_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc_ref(v_env_4195_);
lean_dec(v___x_4194_);
v___x_4196_ = lean_st_ref_get(v___y_4192_);
v_scopes_4197_ = lean_ctor_get(v___x_4196_, 2);
lean_inc(v_scopes_4197_);
lean_dec(v___x_4196_);
v___x_4198_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4199_ = l_List_head_x21___redArg(v___x_4198_, v_scopes_4197_);
lean_dec(v_scopes_4197_);
v_opts_4200_ = lean_ctor_get(v___x_4199_, 1);
lean_inc_ref(v_opts_4200_);
lean_dec(v___x_4199_);
v___x_4201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_4202_ = lean_unsigned_to_nat(32u);
v___x_4203_ = lean_mk_empty_array_with_capacity(v___x_4202_);
lean_dec_ref(v___x_4203_);
v___x_4204_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_4205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4205_, 0, v_env_4195_);
lean_ctor_set(v___x_4205_, 1, v___x_4201_);
lean_ctor_set(v___x_4205_, 2, v___x_4204_);
lean_ctor_set(v___x_4205_, 3, v_opts_4200_);
v___x_4206_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
lean_ctor_set(v___x_4206_, 1, v_msgData_4191_);
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msgData_4208_, v___y_4209_);
lean_dec(v___y_4209_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Lean_Elab_Command_getRef___redArg(v___y_4213_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v_macroStack_4218_; lean_object* v___x_4219_; lean_object* v_a_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4231_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref(v___x_4216_);
v_macroStack_4218_ = lean_ctor_get(v___y_4213_, 4);
v___x_4219_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msg_4212_, v___y_4214_);
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref(v___x_4219_);
lean_inc_n(v_macroStack_4218_, 2);
v___x_4221_ = l_Lean_Elab_getBetterRef(v_a_4217_, v_macroStack_4218_);
lean_dec(v_a_4217_);
v___x_4222_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_a_4220_, v_macroStack_4218_, v___y_4214_);
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4225_ = v___x_4222_;
v_isShared_4226_ = v_isSharedCheck_4231_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4231_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4227_; lean_object* v___x_4229_; 
v___x_4227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4221_);
lean_ctor_set(v___x_4227_, 1, v_a_4223_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set_tag(v___x_4225_, 1);
lean_ctor_set(v___x_4225_, 0, v___x_4227_);
v___x_4229_ = v___x_4225_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
lean_dec_ref(v_msg_4212_);
v_a_4232_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4216_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4216_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4240_, v___y_4241_, v___y_4242_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_4245_, lean_object* v_msg_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Lean_Elab_Command_getRef___redArg(v___y_4247_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_a_4251_; lean_object* v_fileName_4252_; lean_object* v_fileMap_4253_; lean_object* v_currRecDepth_4254_; lean_object* v_cmdPos_4255_; lean_object* v_macroStack_4256_; lean_object* v_quotContext_x3f_4257_; lean_object* v_currMacroScope_4258_; lean_object* v_snap_x3f_4259_; lean_object* v_cancelTk_x3f_4260_; uint8_t v_suppressElabErrors_4261_; lean_object* v_ref_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
lean_inc(v_a_4251_);
lean_dec_ref(v___x_4250_);
v_fileName_4252_ = lean_ctor_get(v___y_4247_, 0);
v_fileMap_4253_ = lean_ctor_get(v___y_4247_, 1);
v_currRecDepth_4254_ = lean_ctor_get(v___y_4247_, 2);
v_cmdPos_4255_ = lean_ctor_get(v___y_4247_, 3);
v_macroStack_4256_ = lean_ctor_get(v___y_4247_, 4);
v_quotContext_x3f_4257_ = lean_ctor_get(v___y_4247_, 5);
v_currMacroScope_4258_ = lean_ctor_get(v___y_4247_, 6);
v_snap_x3f_4259_ = lean_ctor_get(v___y_4247_, 8);
v_cancelTk_x3f_4260_ = lean_ctor_get(v___y_4247_, 9);
v_suppressElabErrors_4261_ = lean_ctor_get_uint8(v___y_4247_, sizeof(void*)*10);
v_ref_4262_ = l_Lean_replaceRef(v_ref_4245_, v_a_4251_);
lean_dec(v_a_4251_);
lean_inc(v_cancelTk_x3f_4260_);
lean_inc(v_snap_x3f_4259_);
lean_inc(v_currMacroScope_4258_);
lean_inc(v_quotContext_x3f_4257_);
lean_inc(v_macroStack_4256_);
lean_inc(v_cmdPos_4255_);
lean_inc(v_currRecDepth_4254_);
lean_inc_ref(v_fileMap_4253_);
lean_inc_ref(v_fileName_4252_);
v___x_4263_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4263_, 0, v_fileName_4252_);
lean_ctor_set(v___x_4263_, 1, v_fileMap_4253_);
lean_ctor_set(v___x_4263_, 2, v_currRecDepth_4254_);
lean_ctor_set(v___x_4263_, 3, v_cmdPos_4255_);
lean_ctor_set(v___x_4263_, 4, v_macroStack_4256_);
lean_ctor_set(v___x_4263_, 5, v_quotContext_x3f_4257_);
lean_ctor_set(v___x_4263_, 6, v_currMacroScope_4258_);
lean_ctor_set(v___x_4263_, 7, v_ref_4262_);
lean_ctor_set(v___x_4263_, 8, v_snap_x3f_4259_);
lean_ctor_set(v___x_4263_, 9, v_cancelTk_x3f_4260_);
lean_ctor_set_uint8(v___x_4263_, sizeof(void*)*10, v_suppressElabErrors_4261_);
v___x_4264_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4246_, v___x_4263_, v___y_4248_);
lean_dec_ref(v___x_4263_);
return v___x_4264_;
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec_ref(v_msg_4246_);
v_a_4265_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4250_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4250_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_4273_, lean_object* v_msg_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4273_, v_msg_4274_, v___y_4275_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v_ref_4273_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_4279_, lean_object* v_msg_4280_, lean_object* v_declHint_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
lean_object* v___x_4285_; lean_object* v_a_4286_; lean_object* v___x_4287_; 
v___x_4285_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_4280_, v_declHint_4281_, v___y_4282_, v___y_4283_);
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref(v___x_4285_);
v___x_4287_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4279_, v_a_4286_, v___y_4282_, v___y_4283_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_4288_, lean_object* v_msg_4289_, lean_object* v_declHint_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4288_, v_msg_4289_, v_declHint_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v_ref_4288_);
return v_res_4294_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4296_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__0));
v___x_4297_ = l_Lean_stringToMessageData(v___x_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_4298_, lean_object* v_constName_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v___x_4303_; uint8_t v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4303_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_4304_ = 0;
lean_inc(v_constName_4299_);
v___x_4305_ = l_Lean_MessageData_ofConstName(v_constName_4299_, v___x_4304_);
v___x_4306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4303_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_4308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4306_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4298_, v___x_4308_, v_constName_4299_, v___y_4300_, v___y_4301_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_4310_, lean_object* v_constName_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_4310_, v_constName_4311_, v___y_4312_, v___y_4313_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec(v_ref_4310_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(lean_object* v_constName_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lean_Elab_Command_getRef___redArg(v___y_4317_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; lean_object* v___x_4322_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4321_);
lean_dec_ref(v___x_4320_);
v___x_4322_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_a_4321_, v_constName_4316_, v___y_4317_, v___y_4318_);
lean_dec(v_a_4321_);
return v___x_4322_;
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec(v_constName_4316_);
v_a_4323_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4320_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4320_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_constName_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4331_, v___y_4332_, v___y_4333_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(lean_object* v_constName_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v___x_4340_; lean_object* v_env_4341_; uint8_t v___x_4342_; lean_object* v___x_4343_; 
v___x_4340_ = lean_st_ref_get(v___y_4338_);
v_env_4341_ = lean_ctor_get(v___x_4340_, 0);
lean_inc_ref(v_env_4341_);
lean_dec(v___x_4340_);
v___x_4342_ = 0;
lean_inc(v_constName_4336_);
v___x_4343_ = l_Lean_Environment_find_x3f(v_env_4341_, v_constName_4336_, v___x_4342_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v___x_4344_; 
v___x_4344_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4336_, v___y_4337_, v___y_4338_);
return v___x_4344_;
}
else
{
lean_object* v_val_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4352_; 
lean_dec(v_constName_4336_);
v_val_4345_ = lean_ctor_get(v___x_4343_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4347_ = v___x_4343_;
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_val_4345_);
lean_dec(v___x_4343_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4350_; 
if (v_isShared_4348_ == 0)
{
lean_ctor_set_tag(v___x_4347_, 0);
v___x_4350_ = v___x_4347_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v_val_4345_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1___boxed(lean_object* v_constName_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_constName_4353_, v___y_4354_, v___y_4355_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(uint8_t v___x_4358_, lean_object* v_x_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
if (lean_obj_tag(v_x_4359_) == 0)
{
uint8_t v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4363_ = 1;
v___x_4364_ = lean_box(v___x_4363_);
v___x_4365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4364_);
return v___x_4365_;
}
else
{
lean_object* v_head_4366_; lean_object* v_tail_4367_; lean_object* v___x_4368_; 
v_head_4366_ = lean_ctor_get(v_x_4359_, 0);
lean_inc(v_head_4366_);
v_tail_4367_ = lean_ctor_get(v_x_4359_, 1);
lean_inc(v_tail_4367_);
lean_dec_ref(v_x_4359_);
v___x_4368_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_head_4366_, v___y_4360_, v___y_4361_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4389_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4371_ = v___x_4368_;
v_isShared_4372_ = v_isSharedCheck_4389_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4368_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4389_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___y_4374_; uint8_t v_a_4375_; 
if (lean_obj_tag(v_a_4369_) == 6)
{
lean_object* v_val_4377_; lean_object* v_numFields_4378_; lean_object* v___x_4379_; uint8_t v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4383_; 
v_val_4377_ = lean_ctor_get(v_a_4369_, 0);
lean_inc_ref(v_val_4377_);
lean_dec_ref(v_a_4369_);
v_numFields_4378_ = lean_ctor_get(v_val_4377_, 4);
lean_inc(v_numFields_4378_);
lean_dec_ref(v_val_4377_);
v___x_4379_ = lean_unsigned_to_nat(0u);
v___x_4380_ = lean_nat_dec_eq(v_numFields_4378_, v___x_4379_);
lean_dec(v_numFields_4378_);
v___x_4381_ = lean_box(v___x_4380_);
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 0, v___x_4381_);
v___x_4383_ = v___x_4371_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4381_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
v___y_4374_ = v___x_4383_;
v_a_4375_ = v___x_4380_;
goto v___jp_4373_;
}
}
else
{
lean_object* v___x_4385_; lean_object* v___x_4387_; 
lean_dec(v_a_4369_);
v___x_4385_ = lean_box(v___x_4358_);
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 0, v___x_4385_);
v___x_4387_ = v___x_4371_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4385_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
v___y_4374_ = v___x_4387_;
v_a_4375_ = v___x_4358_;
goto v___jp_4373_;
}
}
v___jp_4373_:
{
if (v_a_4375_ == 0)
{
lean_dec(v_tail_4367_);
return v___y_4374_;
}
else
{
lean_dec_ref(v___y_4374_);
v_x_4359_ = v_tail_4367_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v_tail_4367_);
v_a_4390_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4368_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4368_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2___boxed(lean_object* v___x_4398_, lean_object* v_x_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
uint8_t v___x_7050__boxed_4403_; lean_object* v_res_4404_; 
v___x_7050__boxed_4403_ = lean_unbox(v___x_4398_);
v_res_4404_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(v___x_7050__boxed_4403_, v_x_4399_, v___y_4400_, v___y_4401_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(lean_object* v_declName_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v___x_4409_; 
v___x_4409_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_declName_4405_, v___y_4406_, v___y_4407_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4465_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4412_ = v___x_4409_;
v_isShared_4413_ = v_isSharedCheck_4465_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4409_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4465_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
if (lean_obj_tag(v_a_4410_) == 5)
{
lean_object* v_val_4414_; lean_object* v_toConstantVal_4415_; lean_object* v_numParams_4416_; lean_object* v_numIndices_4417_; lean_object* v_ctors_4418_; uint8_t v_isRec_4419_; uint8_t v_isUnsafe_4420_; lean_object* v_type_4421_; uint8_t v___x_4422_; 
v_val_4414_ = lean_ctor_get(v_a_4410_, 0);
lean_inc_ref(v_val_4414_);
lean_dec_ref(v_a_4410_);
v_toConstantVal_4415_ = lean_ctor_get(v_val_4414_, 0);
v_numParams_4416_ = lean_ctor_get(v_val_4414_, 1);
lean_inc(v_numParams_4416_);
v_numIndices_4417_ = lean_ctor_get(v_val_4414_, 2);
lean_inc(v_numIndices_4417_);
v_ctors_4418_ = lean_ctor_get(v_val_4414_, 4);
lean_inc(v_ctors_4418_);
v_isRec_4419_ = lean_ctor_get_uint8(v_val_4414_, sizeof(void*)*6);
v_isUnsafe_4420_ = lean_ctor_get_uint8(v_val_4414_, sizeof(void*)*6 + 1);
v_type_4421_ = lean_ctor_get(v_toConstantVal_4415_, 2);
v___x_4422_ = l_Lean_Expr_isProp(v_type_4421_);
if (v___x_4422_ == 0)
{
lean_object* v___x_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v___x_4423_ = l_Lean_InductiveVal_numTypeFormers(v_val_4414_);
lean_dec_ref(v_val_4414_);
v___x_4424_ = lean_unsigned_to_nat(1u);
v___x_4425_ = lean_nat_dec_eq(v___x_4423_, v___x_4424_);
lean_dec(v___x_4423_);
if (v___x_4425_ == 0)
{
lean_object* v___x_4426_; lean_object* v___x_4428_; 
lean_dec(v_ctors_4418_);
lean_dec(v_numIndices_4417_);
lean_dec(v_numParams_4416_);
v___x_4426_ = lean_box(v___x_4425_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4426_);
v___x_4428_ = v___x_4412_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4426_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
else
{
lean_object* v___x_4430_; uint8_t v___x_4431_; 
v___x_4430_ = lean_unsigned_to_nat(0u);
v___x_4431_ = lean_nat_dec_eq(v_numIndices_4417_, v___x_4430_);
lean_dec(v_numIndices_4417_);
if (v___x_4431_ == 0)
{
lean_object* v___x_4432_; lean_object* v___x_4434_; 
lean_dec(v_ctors_4418_);
lean_dec(v_numParams_4416_);
v___x_4432_ = lean_box(v___x_4431_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4432_);
v___x_4434_ = v___x_4412_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4432_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
else
{
uint8_t v___x_4436_; 
v___x_4436_ = lean_nat_dec_eq(v_numParams_4416_, v___x_4430_);
lean_dec(v_numParams_4416_);
if (v___x_4436_ == 0)
{
lean_object* v___x_4437_; lean_object* v___x_4439_; 
lean_dec(v_ctors_4418_);
v___x_4437_ = lean_box(v___x_4436_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4437_);
v___x_4439_ = v___x_4412_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
else
{
uint8_t v___x_4441_; 
v___x_4441_ = l_List_isEmpty___redArg(v_ctors_4418_);
if (v___x_4441_ == 0)
{
if (v_isRec_4419_ == 0)
{
if (v_isUnsafe_4420_ == 0)
{
lean_object* v___x_4442_; 
lean_del_object(v___x_4412_);
v___x_4442_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(v_isUnsafe_4420_, v_ctors_4418_, v___y_4406_, v___y_4407_);
return v___x_4442_;
}
else
{
lean_object* v___x_4443_; lean_object* v___x_4445_; 
lean_dec(v_ctors_4418_);
v___x_4443_ = lean_box(v_isRec_4419_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4443_);
v___x_4445_ = v___x_4412_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
else
{
lean_object* v___x_4447_; lean_object* v___x_4449_; 
lean_dec(v_ctors_4418_);
v___x_4447_ = lean_box(v___x_4441_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4447_);
v___x_4449_ = v___x_4412_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4447_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
else
{
lean_object* v___x_4451_; lean_object* v___x_4453_; 
lean_dec(v_ctors_4418_);
v___x_4451_ = lean_box(v___x_4422_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4451_);
v___x_4453_ = v___x_4412_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4451_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
return v___x_4453_;
}
}
}
}
}
}
else
{
uint8_t v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4458_; 
lean_dec(v_ctors_4418_);
lean_dec(v_numIndices_4417_);
lean_dec(v_numParams_4416_);
lean_dec_ref(v_val_4414_);
v___x_4455_ = 0;
v___x_4456_ = lean_box(v___x_4455_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4456_);
v___x_4458_ = v___x_4412_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4456_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
else
{
uint8_t v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4463_; 
lean_dec(v_a_4410_);
v___x_4460_ = 0;
v___x_4461_ = lean_box(v___x_4460_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4461_);
v___x_4463_ = v___x_4412_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4461_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
else
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
v_a_4466_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4468_ = v___x_4409_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4409_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1___boxed(lean_object* v_declName_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(v_declName_4474_, v___y_4475_, v___y_4476_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(lean_object* v_as_4479_, size_t v_i_4480_, size_t v_stop_4481_, lean_object* v_b_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
uint8_t v___x_4486_; 
v___x_4486_ = lean_usize_dec_eq(v_i_4480_, v_stop_4481_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = lean_array_uget_borrowed(v_as_4479_, v_i_4480_);
lean_inc(v___x_4487_);
v___x_4488_ = l_Lean_Elab_Command_elabCommand(v___x_4487_, v___y_4483_, v___y_4484_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; size_t v___x_4490_; size_t v___x_4491_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref(v___x_4488_);
v___x_4490_ = ((size_t)1ULL);
v___x_4491_ = lean_usize_add(v_i_4480_, v___x_4490_);
v_i_4480_ = v___x_4491_;
v_b_4482_ = v_a_4489_;
goto _start;
}
else
{
return v___x_4488_;
}
}
else
{
lean_object* v___x_4493_; 
v___x_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4493_, 0, v_b_4482_);
return v___x_4493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2___boxed(lean_object* v_as_4494_, lean_object* v_i_4495_, lean_object* v_stop_4496_, lean_object* v_b_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
size_t v_i_boxed_4501_; size_t v_stop_boxed_4502_; lean_object* v_res_4503_; 
v_i_boxed_4501_ = lean_unbox_usize(v_i_4495_);
lean_dec(v_i_4495_);
v_stop_boxed_4502_ = lean_unbox_usize(v_stop_4496_);
lean_dec(v_stop_4496_);
v_res_4503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_as_4494_, v_i_boxed_4501_, v_stop_boxed_4502_, v_b_4497_, v___y_4498_, v___y_4499_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec_ref(v_as_4494_);
return v_res_4503_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11(void){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4531_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10));
v___x_4532_ = l_String_toRawSubstring_x27(v___x_4531_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1(lean_object* v___x_4536_, lean_object* v_declName_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v_a_4545_; lean_object* v___x_4572_; 
v___x_4572_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4536_, v___y_4538_, v___y_4539_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v_a_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4643_; 
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4575_ = v___x_4572_;
v_isShared_4576_ = v_isSharedCheck_4643_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_a_4573_);
lean_dec(v___x_4572_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4643_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___y_4610_; lean_object* v___x_4611_; 
lean_inc(v_declName_4537_);
v___x_4611_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(v_declName_4537_, v___y_4538_, v___y_4539_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___y_4613_; lean_object* v___x_4614_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
lean_inc(v_a_4612_);
lean_dec_ref(v___x_4611_);
lean_inc(v_a_4573_);
v___y_4613_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0___boxed), 10, 3);
lean_closure_set(v___y_4613_, 0, v_a_4612_);
lean_closure_set(v___y_4613_, 1, v_a_4573_);
lean_closure_set(v___y_4613_, 2, v_declName_4537_);
v___x_4614_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_4613_, v___y_4538_, v___y_4539_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; uint8_t v___x_4618_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_a_4615_);
lean_dec_ref(v___x_4614_);
v___x_4616_ = lean_unsigned_to_nat(0u);
v___x_4617_ = lean_array_get_size(v_a_4615_);
v___x_4618_ = lean_nat_dec_lt(v___x_4616_, v___x_4617_);
if (v___x_4618_ == 0)
{
lean_dec(v_a_4615_);
goto v___jp_4577_;
}
else
{
lean_object* v___x_4619_; uint8_t v___x_4620_; 
v___x_4619_ = lean_box(0);
v___x_4620_ = lean_nat_dec_le(v___x_4617_, v___x_4617_);
if (v___x_4620_ == 0)
{
if (v___x_4618_ == 0)
{
lean_dec(v_a_4615_);
goto v___jp_4577_;
}
else
{
size_t v___x_4621_; size_t v___x_4622_; lean_object* v___x_4623_; 
v___x_4621_ = ((size_t)0ULL);
v___x_4622_ = lean_usize_of_nat(v___x_4617_);
v___x_4623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_a_4615_, v___x_4621_, v___x_4622_, v___x_4619_, v___y_4538_, v___y_4539_);
lean_dec(v_a_4615_);
v___y_4610_ = v___x_4623_;
goto v___jp_4609_;
}
}
else
{
size_t v___x_4624_; size_t v___x_4625_; lean_object* v___x_4626_; 
v___x_4624_ = ((size_t)0ULL);
v___x_4625_ = lean_usize_of_nat(v___x_4617_);
v___x_4626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_a_4615_, v___x_4624_, v___x_4625_, v___x_4619_, v___y_4538_, v___y_4539_);
lean_dec(v_a_4615_);
v___y_4610_ = v___x_4626_;
goto v___jp_4609_;
}
}
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
lean_del_object(v___x_4575_);
lean_dec(v_a_4573_);
lean_dec_ref(v___y_4538_);
v_a_4627_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4614_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4614_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
else
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
lean_del_object(v___x_4575_);
lean_dec(v_a_4573_);
lean_dec_ref(v___y_4538_);
lean_dec(v_declName_4537_);
v_a_4635_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4611_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4611_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_a_4635_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
v___jp_4577_:
{
uint8_t v_usePartial_4578_; 
v_usePartial_4578_ = lean_ctor_get_uint8(v_a_4573_, sizeof(void*)*3);
if (v_usePartial_4578_ == 0)
{
lean_object* v_instName_4579_; lean_object* v___x_4580_; 
lean_del_object(v___x_4575_);
v_instName_4579_ = lean_ctor_get(v_a_4573_, 0);
lean_inc(v_instName_4579_);
lean_dec(v_a_4573_);
v___x_4580_ = l_Lean_Elab_Command_getRef___redArg(v___y_4538_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4582_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
lean_inc(v_a_4581_);
lean_dec_ref(v___x_4580_);
v___x_4582_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_4538_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v_quotContext_x3f_4584_; lean_object* v___x_4585_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4583_);
lean_dec_ref(v___x_4582_);
v_quotContext_x3f_4584_ = lean_ctor_get(v___y_4538_, 5);
v___x_4585_ = l_Lean_SourceInfo_fromRef(v_a_4581_, v_usePartial_4578_);
lean_dec(v_a_4581_);
if (lean_obj_tag(v_quotContext_x3f_4584_) == 0)
{
lean_object* v___x_4586_; lean_object* v_a_4587_; 
v___x_4586_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_4539_);
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4587_);
lean_dec_ref(v___x_4586_);
v___y_4542_ = v_a_4583_;
v___y_4543_ = v___x_4585_;
v___y_4544_ = v_instName_4579_;
v_a_4545_ = v_a_4587_;
goto v___jp_4541_;
}
else
{
lean_object* v_val_4588_; 
v_val_4588_ = lean_ctor_get(v_quotContext_x3f_4584_, 0);
lean_inc(v_val_4588_);
v___y_4542_ = v_a_4583_;
v___y_4543_ = v___x_4585_;
v___y_4544_ = v_instName_4579_;
v_a_4545_ = v_val_4588_;
goto v___jp_4541_;
}
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
lean_dec(v_a_4581_);
lean_dec(v_instName_4579_);
lean_dec_ref(v___y_4538_);
v_a_4589_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___x_4582_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___x_4582_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_a_4589_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
else
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
lean_dec(v_instName_4579_);
lean_dec_ref(v___y_4538_);
v_a_4597_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___x_4580_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4580_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
}
else
{
lean_object* v___x_4605_; lean_object* v___x_4607_; 
lean_dec(v_a_4573_);
lean_dec_ref(v___y_4538_);
v___x_4605_ = lean_box(0);
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 0, v___x_4605_);
v___x_4607_ = v___x_4575_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4605_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
v___jp_4609_:
{
if (lean_obj_tag(v___y_4610_) == 0)
{
lean_dec_ref(v___y_4610_);
goto v___jp_4577_;
}
else
{
lean_del_object(v___x_4575_);
lean_dec(v_a_4573_);
lean_dec_ref(v___y_4538_);
return v___y_4610_;
}
}
}
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
lean_dec_ref(v___y_4538_);
lean_dec(v_declName_4537_);
v_a_4644_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4572_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4572_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
v___jp_4541_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4546_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0));
v___x_4547_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1));
lean_inc_n(v___y_4543_, 10);
v___x_4548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___y_4543_);
lean_ctor_set(v___x_4548_, 1, v___x_4546_);
v___x_4549_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2));
v___x_4550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4550_, 0, v___y_4543_);
lean_ctor_set(v___x_4550_, 1, v___x_4549_);
v___x_4551_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_4552_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4));
v___x_4553_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6));
v___x_4554_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_4555_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4555_, 0, v___y_4543_);
lean_ctor_set(v___x_4555_, 1, v___x_4551_);
lean_ctor_set(v___x_4555_, 2, v___x_4554_);
lean_inc_ref(v___x_4555_);
v___x_4556_ = l_Lean_Syntax_node1(v___y_4543_, v___x_4553_, v___x_4555_);
v___x_4557_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9));
v___x_4558_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11);
v___x_4559_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__12));
v___x_4560_ = l_Lean_addMacroScope(v_a_4545_, v___x_4559_, v___y_4542_);
v___x_4561_ = lean_box(0);
v___x_4562_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4562_, 0, v___y_4543_);
lean_ctor_set(v___x_4562_, 1, v___x_4558_);
lean_ctor_set(v___x_4562_, 2, v___x_4560_);
lean_ctor_set(v___x_4562_, 3, v___x_4561_);
v___x_4563_ = l_Lean_Syntax_node2(v___y_4543_, v___x_4557_, v___x_4562_, v___x_4555_);
v___x_4564_ = l_Lean_Syntax_node2(v___y_4543_, v___x_4552_, v___x_4556_, v___x_4563_);
v___x_4565_ = l_Lean_Syntax_node1(v___y_4543_, v___x_4551_, v___x_4564_);
v___x_4566_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__13));
v___x_4567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___y_4543_);
lean_ctor_set(v___x_4567_, 1, v___x_4566_);
v___x_4568_ = lean_mk_syntax_ident(v___y_4544_);
v___x_4569_ = l_Lean_Syntax_node1(v___y_4543_, v___x_4551_, v___x_4568_);
v___x_4570_ = l_Lean_Syntax_node5(v___y_4543_, v___x_4547_, v___x_4548_, v___x_4550_, v___x_4565_, v___x_4567_, v___x_4569_);
v___x_4571_ = l_Lean_Elab_Command_elabCommand(v___x_4570_, v___y_4538_, v___y_4539_);
lean_dec_ref(v___y_4538_);
return v___x_4571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___boxed(lean_object* v___x_4652_, lean_object* v_declName_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1(v___x_4652_, v_declName_4653_, v___y_4654_, v___y_4655_);
lean_dec(v___y_4655_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(lean_object* v_declName_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; uint8_t v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___f_4667_; lean_object* v___x_4668_; 
v___x_4662_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_4663_ = ((lean_object*)(l_Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_4664_ = 1;
v___x_4665_ = lean_box(v___x_4664_);
lean_inc_n(v_declName_4658_, 2);
v___x_4666_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_mkContext___boxed), 11, 4);
lean_closure_set(v___x_4666_, 0, v___x_4662_);
lean_closure_set(v___x_4666_, 1, v___x_4663_);
lean_closure_set(v___x_4666_, 2, v_declName_4658_);
lean_closure_set(v___x_4666_, 3, v___x_4665_);
v___f_4667_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___boxed), 5, 2);
lean_closure_set(v___f_4667_, 0, v___x_4666_);
lean_closure_set(v___f_4667_, 1, v_declName_4658_);
v___x_4668_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_4658_, v___f_4667_, v_a_4659_, v_a_4660_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___boxed(lean_object* v_declName_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(v_declName_4669_, v_a_4670_, v_a_4671_);
lean_dec(v_a_4671_);
lean_dec_ref(v_a_4670_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_4674_, lean_object* v_constName_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_){
_start:
{
lean_object* v___x_4679_; 
v___x_4679_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4675_, v___y_4676_, v___y_4677_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4680_, lean_object* v_constName_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2(v_00_u03b1_4680_, v_constName_4681_, v___y_4682_, v___y_4683_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_4686_, lean_object* v_ref_4687_, lean_object* v_constName_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v___x_4692_; 
v___x_4692_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_4687_, v_constName_4688_, v___y_4689_, v___y_4690_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4693_, lean_object* v_ref_4694_, lean_object* v_constName_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v_res_4699_; 
v_res_4699_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_4693_, v_ref_4694_, v_constName_4695_, v___y_4696_, v___y_4697_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v_ref_4694_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4700_, lean_object* v_ref_4701_, lean_object* v_msg_4702_, lean_object* v_declHint_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4701_, v_msg_4702_, v_declHint_4703_, v___y_4704_, v___y_4705_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4708_, lean_object* v_ref_4709_, lean_object* v_msg_4710_, lean_object* v_declHint_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_4708_, v_ref_4709_, v_msg_4710_, v_declHint_4711_, v___y_4712_, v___y_4713_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec(v_ref_4709_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_4716_, lean_object* v_declHint_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4716_, v_declHint_4717_, v___y_4719_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_4722_, lean_object* v_declHint_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8(v_msg_4722_, v_declHint_4723_, v___y_4724_, v___y_4725_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_4728_, lean_object* v_ref_4729_, lean_object* v_msg_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_){
_start:
{
lean_object* v___x_4734_; 
v___x_4734_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4729_, v_msg_4730_, v___y_4731_, v___y_4732_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_4735_, lean_object* v_ref_4736_, lean_object* v_msg_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_){
_start:
{
lean_object* v_res_4741_; 
v_res_4741_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_4735_, v_ref_4736_, v_msg_4737_, v___y_4738_, v___y_4739_);
lean_dec(v___y_4739_);
lean_dec_ref(v___y_4738_);
lean_dec(v_ref_4736_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v___x_4746_; 
v___x_4746_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msgData_4742_, v___y_4744_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
lean_object* v_res_4751_; 
v_res_4751_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_4747_, v___y_4748_, v___y_4749_);
lean_dec(v___y_4749_);
lean_dec_ref(v___y_4748_);
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_4752_, lean_object* v_msg_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_){
_start:
{
lean_object* v___x_4757_; 
v___x_4757_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4753_, v___y_4754_, v___y_4755_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4758_, lean_object* v_msg_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_4758_, v_msg_4759_, v___y_4760_, v___y_4761_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12(lean_object* v_msgData_4764_, lean_object* v_macroStack_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_msgData_4764_, v_macroStack_4765_, v___y_4767_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___boxed(lean_object* v_msgData_4770_, lean_object* v_macroStack_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12(v_msgData_4770_, v_macroStack_4771_, v___y_4772_, v___y_4773_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(lean_object* v_declName_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v___x_4779_; lean_object* v_env_4780_; uint8_t v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4779_ = lean_st_ref_get(v___y_4777_);
v_env_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc_ref(v_env_4780_);
lean_dec(v___x_4779_);
v___x_4781_ = l_Lean_isInductiveCore(v_env_4780_, v_declName_4776_);
v___x_4782_ = lean_box(v___x_4781_);
v___x_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4782_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v_declName_4784_, v___y_4785_);
lean_dec(v___y_4785_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1(lean_object* v_declName_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_){
_start:
{
lean_object* v___x_4792_; 
v___x_4792_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v_declName_4788_, v___y_4790_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___boxed(lean_object* v_declName_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1(v_declName_4793_, v___y_4794_, v___y_4795_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(uint8_t v_____do__lift_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
if (v_____do__lift_4798_ == 0)
{
uint8_t v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4802_ = 1;
v___x_4803_ = lean_box(v___x_4802_);
v___x_4804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4803_);
return v___x_4804_;
}
else
{
uint8_t v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4805_ = 0;
v___x_4806_ = lean_box(v___x_4805_);
v___x_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4806_);
return v___x_4807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
uint8_t v_____do__lift_1736__boxed_4812_; lean_object* v_res_4813_; 
v_____do__lift_1736__boxed_4812_ = lean_unbox(v_____do__lift_4808_);
v_res_4813_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v_____do__lift_1736__boxed_4812_, v___y_4809_, v___y_4810_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
return v_res_4813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(lean_object* v_as_4814_, size_t v_i_4815_, size_t v_stop_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
uint8_t v___x_4820_; 
v___x_4820_ = lean_usize_dec_eq(v_i_4815_, v_stop_4816_);
if (v___x_4820_ == 0)
{
uint8_t v___x_4821_; uint8_t v_a_4823_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4821_ = 1;
v___x_4829_ = lean_array_uget_borrowed(v_as_4814_, v_i_4815_);
lean_inc(v___x_4829_);
v___x_4830_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v___x_4829_, v___y_4818_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4840_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4833_ = v___x_4830_;
v_isShared_4834_ = v_isSharedCheck_4840_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4830_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4840_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
uint8_t v___x_4835_; 
v___x_4835_ = lean_unbox(v_a_4831_);
lean_dec(v_a_4831_);
if (v___x_4835_ == 0)
{
lean_object* v___x_4836_; lean_object* v___x_4838_; 
v___x_4836_ = lean_box(v___x_4821_);
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 0, v___x_4836_);
v___x_4838_ = v___x_4833_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4836_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
else
{
lean_del_object(v___x_4833_);
v_a_4823_ = v___x_4820_;
goto v___jp_4822_;
}
}
}
else
{
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4841_; uint8_t v___x_4842_; 
v_a_4841_ = lean_ctor_get(v___x_4830_, 0);
lean_inc(v_a_4841_);
lean_dec_ref(v___x_4830_);
v___x_4842_ = lean_unbox(v_a_4841_);
lean_dec(v_a_4841_);
v_a_4823_ = v___x_4842_;
goto v___jp_4822_;
}
else
{
return v___x_4830_;
}
}
v___jp_4822_:
{
if (v_a_4823_ == 0)
{
size_t v___x_4824_; size_t v___x_4825_; 
v___x_4824_ = ((size_t)1ULL);
v___x_4825_ = lean_usize_add(v_i_4815_, v___x_4824_);
v_i_4815_ = v___x_4825_;
goto _start;
}
else
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = lean_box(v___x_4821_);
v___x_4828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4827_);
return v___x_4828_;
}
}
}
else
{
uint8_t v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4843_ = 0;
v___x_4844_ = lean_box(v___x_4843_);
v___x_4845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4844_);
return v___x_4845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2___boxed(lean_object* v_as_4846_, lean_object* v_i_4847_, lean_object* v_stop_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_){
_start:
{
size_t v_i_boxed_4852_; size_t v_stop_boxed_4853_; lean_object* v_res_4854_; 
v_i_boxed_4852_ = lean_unbox_usize(v_i_4847_);
lean_dec(v_i_4847_);
v_stop_boxed_4853_ = lean_unbox_usize(v_stop_4848_);
lean_dec(v_stop_4848_);
v_res_4854_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(v_as_4846_, v_i_boxed_4852_, v_stop_boxed_4853_, v___y_4849_, v___y_4850_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec_ref(v_as_4846_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(lean_object* v_as_4855_, size_t v_sz_4856_, size_t v_i_4857_, lean_object* v_b_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
uint8_t v___x_4862_; 
v___x_4862_ = lean_usize_dec_lt(v_i_4857_, v_sz_4856_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4863_; 
v___x_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4863_, 0, v_b_4858_);
return v___x_4863_;
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4865_; 
v_a_4864_ = lean_array_uget_borrowed(v_as_4855_, v_i_4857_);
lean_inc(v_a_4864_);
v___x_4865_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(v_a_4864_, v___y_4859_, v___y_4860_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v___x_4866_; size_t v___x_4867_; size_t v___x_4868_; 
lean_dec_ref(v___x_4865_);
v___x_4866_ = lean_box(0);
v___x_4867_ = ((size_t)1ULL);
v___x_4868_ = lean_usize_add(v_i_4857_, v___x_4867_);
v_i_4857_ = v___x_4868_;
v_b_4858_ = v___x_4866_;
goto _start;
}
else
{
return v___x_4865_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0___boxed(lean_object* v_as_4870_, lean_object* v_sz_4871_, lean_object* v_i_4872_, lean_object* v_b_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
size_t v_sz_boxed_4877_; size_t v_i_boxed_4878_; lean_object* v_res_4879_; 
v_sz_boxed_4877_ = lean_unbox_usize(v_sz_4871_);
lean_dec(v_sz_4871_);
v_i_boxed_4878_ = lean_unbox_usize(v_i_4872_);
lean_dec(v_i_4872_);
v_res_4879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(v_as_4870_, v_sz_boxed_4877_, v_i_boxed_4878_, v_b_4873_, v___y_4874_, v___y_4875_);
lean_dec(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec_ref(v_as_4870_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler(lean_object* v_declNames_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_){
_start:
{
lean_object* v___y_4908_; lean_object* v___x_4911_; lean_object* v___x_4912_; uint8_t v___x_4913_; 
v___x_4911_ = lean_unsigned_to_nat(0u);
v___x_4912_ = lean_array_get_size(v_declNames_4880_);
v___x_4913_ = lean_nat_dec_lt(v___x_4911_, v___x_4912_);
if (v___x_4913_ == 0)
{
lean_object* v___x_4914_; 
v___x_4914_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v___x_4913_, v_a_4881_, v_a_4882_);
v___y_4908_ = v___x_4914_;
goto v___jp_4907_;
}
else
{
if (v___x_4913_ == 0)
{
goto v___jp_4884_;
}
else
{
size_t v___x_4915_; size_t v___x_4916_; lean_object* v___x_4917_; 
v___x_4915_ = ((size_t)0ULL);
v___x_4916_ = lean_usize_of_nat(v___x_4912_);
v___x_4917_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(v_declNames_4880_, v___x_4915_, v___x_4916_, v_a_4881_, v_a_4882_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; uint8_t v___x_4919_; lean_object* v___x_4920_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
lean_inc(v_a_4918_);
lean_dec_ref(v___x_4917_);
v___x_4919_ = lean_unbox(v_a_4918_);
lean_dec(v_a_4918_);
v___x_4920_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v___x_4919_, v_a_4881_, v_a_4882_);
v___y_4908_ = v___x_4920_;
goto v___jp_4907_;
}
else
{
v___y_4908_ = v___x_4917_;
goto v___jp_4907_;
}
}
}
v___jp_4884_:
{
lean_object* v___x_4885_; size_t v_sz_4886_; size_t v___x_4887_; lean_object* v___x_4888_; 
v___x_4885_ = lean_box(0);
v_sz_4886_ = lean_array_size(v_declNames_4880_);
v___x_4887_ = ((size_t)0ULL);
v___x_4888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(v_declNames_4880_, v_sz_4886_, v___x_4887_, v___x_4885_, v_a_4881_, v_a_4882_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4897_; 
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4897_ == 0)
{
lean_object* v_unused_4898_; 
v_unused_4898_ = lean_ctor_get(v___x_4888_, 0);
lean_dec(v_unused_4898_);
v___x_4890_ = v___x_4888_;
v_isShared_4891_ = v_isSharedCheck_4897_;
goto v_resetjp_4889_;
}
else
{
lean_dec(v___x_4888_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4897_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
uint8_t v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4895_; 
v___x_4892_ = 1;
v___x_4893_ = lean_box(v___x_4892_);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 0, v___x_4893_);
v___x_4895_ = v___x_4890_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
v_a_4899_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___x_4888_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4888_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
v___jp_4907_:
{
if (lean_obj_tag(v___y_4908_) == 0)
{
lean_object* v_a_4909_; uint8_t v___x_4910_; 
v_a_4909_ = lean_ctor_get(v___y_4908_, 0);
v___x_4910_ = lean_unbox(v_a_4909_);
if (v___x_4910_ == 0)
{
return v___y_4908_;
}
else
{
lean_dec_ref(v___y_4908_);
goto v___jp_4884_;
}
}
else
{
return v___y_4908_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___boxed(lean_object* v_declNames_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_){
_start:
{
lean_object* v_res_4925_; 
v_res_4925_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler(v_declNames_4921_, v_a_4922_, v_a_4923_);
lean_dec(v_a_4923_);
lean_dec_ref(v_a_4922_);
lean_dec_ref(v_declNames_4921_);
return v_res_4925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4993_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_4994_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_));
v___x_4995_ = l_Lean_Elab_registerDerivingHandler(v___x_4993_, v___x_4994_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v___x_4996_; uint8_t v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
lean_dec_ref(v___x_4995_);
v___x_4996_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_4997_ = 0;
v___x_4998_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_));
v___x_4999_ = l_Lean_registerTraceClass(v___x_4996_, v___x_4997_, v___x_4998_);
return v___x_4999_;
}
else
{
return v___x_4995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2____boxed(lean_object* v_a_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_();
return v_res_5001_;
}
}
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_BEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_deriving_beq_linear__construction__threshold = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_deriving_beq_linear__construction__threshold);
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_BEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin);
lean_object* initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* initialize_Init_Data_Array_OfFn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_BEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_BEq(builtin);
}
#ifdef __cplusplus
}
#endif
