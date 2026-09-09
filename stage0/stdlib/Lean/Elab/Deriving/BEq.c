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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "linear_construction_threshold"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 127, 229, 132, 157, 42, 70, 134)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(155, 188, 150, 126, 202, 210, 87, 56)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(2, 35, 48, 234, 208, 30, 169, 118)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 350, .m_capacity = 350, .m_length = 349, .m_data = "If the inductive data type has this many or more constructors, use a different implementation for implementing `BEq` that avoids the quadratic code size produced by the default implementation.\n\nThe alternative construction compiles to less efficient code in some cases, so by default it is only used for inductive types with 10 or more constructors."};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(254, 165, 225, 156, 115, 202, 230, 35)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(71, 221, 4, 81, 40, 1, 30, 26)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 242, 38, 149, 146, 119, 211, 138)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(120, 78, 208, 242, 44, 150, 100, 230)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 129, 112, 189, 241, 241, 163, 103)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(222, 208, 129, 142, 173, 19, 33, 85)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(71, 160, 64, 149, 162, 78, 171, 187)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 92, 31, 179, 36, 246, 140, 67)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 196, 248, 71, 32, 17, 147, 163)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_deriving_beq_linear__construction__threshold;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(197, 49, 98, 208, 150, 151, 163, 74)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimTarget"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__30_value),LEAN_SCALAR_PTR_LITERAL(136, 63, 46, 91, 99, 29, 205, 171)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__34_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 26, 2, 19, 145, 121, 166, 213)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__41_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__42_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__43_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__44_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__45_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__6_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Nat.decEq"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decEq"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__10_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__11_value),LEAN_SCALAR_PTR_LITERAL(13, 188, 70, 193, 211, 173, 121, 176)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__13_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__15_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__17_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value),LEAN_SCALAR_PTR_LITERAL(125, 82, 240, 34, 69, 121, 64, 234)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27_value),LEAN_SCALAR_PTR_LITERAL(113, 70, 3, 12, 31, 103, 230, 247)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__23_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__35 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__35_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__36 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__36_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__37 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__37_value;
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__5_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__8_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(155, 20, 163, 238, 100, 115, 187, 44)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__17_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__16_value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__19_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__21_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__24_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__25_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "set_option"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 204, 183, 225, 123, 221, 75, 96)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 135, 164, 219, 193, 11, 15, 193)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 118, 133, 101, 222, 86, 142, 163)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(47, 129, 53, 81, 247, 98, 179, 247)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 213, 169, 55, 145, 123, 160, 112)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(71, 28, 210, 8, 101, 35, 72, 179)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 53, 125, 167, 22, 113, 17, 93)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)(((size_t)(993467269) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(40, 184, 182, 130, 80, 10, 154, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 174, 45, 45, 68, 195, 231, 187)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 45, 241, 81, 166, 228, 249, 231)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(98, 175, 82, 143, 146, 81, 47, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_28_, lean_object* v_decl_29_, lean_object* v_ref_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(v_name_28_, v_decl_29_, v_ref_30_);
lean_dec_ref(v_decl_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_91_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_92_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_93_ = l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4__spec__0(v___x_90_, v___x_91_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4____boxed(lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_();
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(lean_object* v_indVal_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_107_ = lean_unsigned_to_nat(2u);
v___x_108_ = l_Lean_Elab_Deriving_mkHeader(v___x_106_, v___x_107_, v_indVal_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___boxed(lean_object* v_indVal_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(v_indVal_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_ref_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_ref_125_ = lean_ctor_get(v___y_122_, 2);
v___x_126_ = 0;
v___x_127_ = l_Lean_SourceInfo_fromRef(v_ref_125_, v___x_126_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0___boxed(lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(lean_object* v_upperBound_146_, lean_object* v_a_147_, lean_object* v_b_148_, lean_object* v___y_149_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_lt(v_a_147_, v_upperBound_146_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
lean_dec(v_a_147_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v_b_148_);
return v___x_152_;
}
else
{
lean_object* v_ref_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_ref_153_ = lean_ctor_get(v___y_149_, 2);
v___x_154_ = 0;
v___x_155_ = l_Lean_SourceInfo_fromRef(v_ref_153_, v___x_154_);
v___x_156_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_157_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
lean_inc(v___x_155_);
v___x_158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_155_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = l_Lean_Syntax_node1(v___x_155_, v___x_156_, v___x_158_);
v___x_160_ = lean_array_push(v_b_148_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_add(v_a_147_, v___x_161_);
lean_dec(v_a_147_);
v_a_147_ = v___x_162_;
v_b_148_ = v___x_160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___boxed(lean_object* v_upperBound_164_, lean_object* v_a_165_, lean_object* v_b_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_upperBound_164_, v_a_165_, v_b_166_, v___y_167_);
lean_dec_ref(v___y_167_);
lean_dec(v_upperBound_164_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(size_t v_sz_170_, size_t v_i_171_, lean_object* v_bs_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = lean_usize_dec_lt(v_i_171_, v_sz_170_);
if (v___x_173_ == 0)
{
return v_bs_172_;
}
else
{
lean_object* v_v_174_; lean_object* v___x_175_; lean_object* v_bs_x27_176_; size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v_v_174_ = lean_array_uget(v_bs_172_, v_i_171_);
v___x_175_ = lean_unsigned_to_nat(0u);
v_bs_x27_176_ = lean_array_uset(v_bs_172_, v_i_171_, v___x_175_);
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_add(v_i_171_, v___x_177_);
v___x_179_ = lean_array_uset(v_bs_x27_176_, v_i_171_, v_v_174_);
v_i_171_ = v___x_178_;
v_bs_172_ = v___x_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0___boxed(lean_object* v_sz_181_, lean_object* v_i_182_, lean_object* v_bs_183_){
_start:
{
size_t v_sz_boxed_184_; size_t v_i_boxed_185_; lean_object* v_res_186_; 
v_sz_boxed_184_ = lean_unbox_usize(v_sz_181_);
lean_dec(v_sz_181_);
v_i_boxed_185_ = lean_unbox_usize(v_i_182_);
lean_dec(v_i_182_);
v_res_186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_boxed_184_, v_i_boxed_185_, v_bs_183_);
return v_res_186_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__1));
v___x_191_ = l_String_toRawSubstring_x27(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13(void){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Array_mkArray0(lean_box(0));
return v___x_214_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__14));
v___x_217_ = l_Lean_mkAtom(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(lean_object* v_indVal_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_numIndices_227_; lean_object* v___x_228_; lean_object* v_patterns_229_; lean_object* v___x_230_; 
v_numIndices_227_ = lean_ctor_get(v_indVal_219_, 2);
v___x_228_ = lean_unsigned_to_nat(0u);
v_patterns_229_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
v___x_230_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_numIndices_227_, v___x_228_, v_patterns_229_, v_a_224_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v_toCold_232_; lean_object* v_ref_233_; lean_object* v___x_234_; lean_object* v_a_235_; lean_object* v___x_236_; lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_275_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v_toCold_232_ = lean_ctor_get(v_a_224_, 0);
v_ref_233_ = lean_ctor_get(v_a_224_, 2);
v___x_234_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref(v___x_234_);
v___x_236_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___lam__0(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_275_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_275_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_275_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v_quotContext_245_; lean_object* v_currMacroScope_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; size_t v_sz_261_; size_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_241_ = 0;
v___x_242_ = l_Lean_SourceInfo_fromRef(v_ref_233_, v___x_241_);
v___x_243_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
lean_inc(v___x_242_);
v___x_244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v_quotContext_245_ = lean_ctor_get(v_toCold_232_, 8);
v_currMacroScope_246_ = lean_ctor_get(v_toCold_232_, 9);
v___x_247_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_248_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_249_ = l_Lean_Syntax_node1(v___x_242_, v___x_248_, v___x_244_);
lean_inc(v___x_249_);
v___x_250_ = lean_array_push(v_a_231_, v___x_249_);
v___x_251_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_252_ = lean_array_push(v___x_250_, v___x_249_);
lean_inc(v_currMacroScope_246_);
lean_inc(v_quotContext_245_);
v___x_253_ = l_Lean_addMacroScope(v_quotContext_245_, v___x_251_, v_currMacroScope_246_);
v___x_254_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7));
v___x_255_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_255_, 0, v_a_235_);
lean_ctor_set(v___x_255_, 1, v___x_247_);
lean_ctor_set(v___x_255_, 2, v___x_253_);
lean_ctor_set(v___x_255_, 3, v___x_254_);
v___x_256_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_257_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
lean_inc_n(v_a_237_, 4);
v___x_258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_258_, 0, v_a_237_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_260_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v_sz_261_ = lean_array_size(v___x_252_);
v___x_262_ = ((size_t)0ULL);
v___x_263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_261_, v___x_262_, v___x_252_);
v___x_264_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_265_ = l_Lean_mkSepArray(v___x_263_, v___x_264_);
lean_dec_ref(v___x_263_);
v___x_266_ = l_Array_append___redArg(v___x_260_, v___x_265_);
lean_dec_ref(v___x_265_);
v___x_267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_267_, 0, v_a_237_);
lean_ctor_set(v___x_267_, 1, v___x_259_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
v___x_268_ = l_Lean_Syntax_node1(v_a_237_, v___x_259_, v___x_267_);
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_270_, 0, v_a_237_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = l_Lean_Syntax_node4(v_a_237_, v___x_256_, v___x_258_, v___x_268_, v___x_270_, v___x_255_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_271_);
v___x_273_ = v___x_239_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
v_a_276_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_230_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_230_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___boxed(lean_object* v_indVal_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(v_indVal_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec_ref(v_indVal_284_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1(lean_object* v_upperBound_293_, lean_object* v_inst_294_, lean_object* v_R_295_, lean_object* v_a_296_, lean_object* v_b_297_, lean_object* v_c_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_upperBound_293_, v_a_296_, v_b_297_, v___y_303_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___boxed(lean_object* v_upperBound_307_, lean_object* v_inst_308_, lean_object* v_R_309_, lean_object* v_a_310_, lean_object* v_b_311_, lean_object* v_c_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1(v_upperBound_307_, v_inst_308_, v_R_309_, v_a_310_, v_b_311_, v_c_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v_upperBound_307_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(lean_object* v_k_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v_b_324_, lean_object* v_c_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; 
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
v___x_331_ = lean_apply_9(v_k_321_, v_b_324_, v_c_325_, v___y_322_, v___y_323_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, lean_box(0));
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed(lean_object* v_k_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v_b_335_, lean_object* v_c_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0(v_k_332_, v___y_333_, v___y_334_, v_b_335_, v_c_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(lean_object* v_type_343_, lean_object* v_k_344_, uint8_t v_cleanupAnnotations_345_, uint8_t v_whnfType_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___f_354_; lean_object* v___x_355_; 
lean_inc(v___y_348_);
lean_inc_ref(v___y_347_);
v___f_354_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_354_, 0, v_k_344_);
lean_closure_set(v___f_354_, 1, v___y_347_);
lean_closure_set(v___f_354_, 2, v___y_348_);
v___x_355_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_343_, v___f_354_, v_cleanupAnnotations_345_, v_whnfType_346_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
if (lean_obj_tag(v___x_355_) == 0)
{
return v___x_355_;
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object* v_type_364_, lean_object* v_k_365_, lean_object* v_cleanupAnnotations_366_, lean_object* v_whnfType_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_375_; uint8_t v_whnfType_boxed_376_; lean_object* v_res_377_; 
v_cleanupAnnotations_boxed_375_ = lean_unbox(v_cleanupAnnotations_366_);
v_whnfType_boxed_376_ = lean_unbox(v_whnfType_367_);
v_res_377_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_364_, v_k_365_, v_cleanupAnnotations_boxed_375_, v_whnfType_boxed_376_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4(lean_object* v_00_u03b1_378_, lean_object* v_type_379_, lean_object* v_k_380_, uint8_t v_cleanupAnnotations_381_, uint8_t v_whnfType_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_379_, v_k_380_, v_cleanupAnnotations_381_, v_whnfType_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___boxed(lean_object* v_00_u03b1_391_, lean_object* v_type_392_, lean_object* v_k_393_, lean_object* v_cleanupAnnotations_394_, lean_object* v_whnfType_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_403_; uint8_t v_whnfType_boxed_404_; lean_object* v_res_405_; 
v_cleanupAnnotations_boxed_403_ = lean_unbox(v_cleanupAnnotations_394_);
v_whnfType_boxed_404_ = lean_unbox(v_whnfType_395_);
v_res_405_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4(v_00_u03b1_391_, v_type_392_, v_k_393_, v_cleanupAnnotations_boxed_403_, v_whnfType_boxed_404_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(lean_object* v___x_406_, lean_object* v_as_407_, size_t v_i_408_, size_t v_stop_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
uint8_t v___x_415_; 
v___x_415_ = lean_usize_dec_eq(v_i_408_, v_stop_409_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_array_uget_borrowed(v_as_407_, v_i_408_);
lean_inc(v___y_413_);
lean_inc_ref(v___y_412_);
lean_inc(v___y_411_);
lean_inc_ref(v___y_410_);
lean_inc(v___x_416_);
v___x_417_ = lean_infer_type(v___x_416_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_431_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_431_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_431_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_431_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = l_Lean_Expr_fvarId_x21(v___x_406_);
v___x_423_ = l_Lean_Expr_containsFVar(v_a_418_, v___x_422_);
lean_dec(v___x_422_);
lean_dec(v_a_418_);
if (v___x_423_ == 0)
{
size_t v___x_424_; size_t v___x_425_; 
lean_del_object(v___x_420_);
v___x_424_ = ((size_t)1ULL);
v___x_425_ = lean_usize_add(v_i_408_, v___x_424_);
v_i_408_ = v___x_425_;
goto _start;
}
else
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = lean_box(v___x_423_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_427_);
v___x_429_ = v___x_420_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_a_432_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_417_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_417_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
else
{
uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = 0;
v___x_441_ = lean_box(v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object* v___x_443_, lean_object* v_as_444_, lean_object* v_i_445_, lean_object* v_stop_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
size_t v_i_boxed_452_; size_t v_stop_boxed_453_; lean_object* v_res_454_; 
v_i_boxed_452_ = lean_unbox_usize(v_i_445_);
lean_dec(v_i_445_);
v_stop_boxed_453_ = lean_unbox_usize(v_stop_446_);
lean_dec(v_stop_446_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_443_, v_as_444_, v_i_boxed_452_, v_stop_boxed_453_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec_ref(v_as_444_);
lean_dec_ref(v___x_443_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_ref_462_; uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_ref_462_ = lean_ctor_get(v___y_459_, 2);
v___x_463_ = 0;
v___x_464_ = l_Lean_SourceInfo_fromRef(v_ref_462_, v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0___boxed(lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
return v_res_473_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__15));
v___x_498_ = l_String_toRawSubstring_x27(v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39));
v___x_553_ = l_String_toRawSubstring_x27(v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__53));
v___x_590_ = l_String_toRawSubstring_x27(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(lean_object* v_upperBound_624_, lean_object* v_indVal_625_, lean_object* v___x_626_, lean_object* v_xs_627_, lean_object* v_a_628_, lean_object* v_auxFunName_629_, lean_object* v_a_630_, lean_object* v_b_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_a_640_; uint8_t v___x_644_; 
v___x_644_ = lean_nat_dec_lt(v_a_630_, v_upperBound_624_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v_b_631_);
return v___x_645_;
}
else
{
lean_object* v_snd_646_; lean_object* v_snd_647_; lean_object* v_fst_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_990_; 
v_snd_646_ = lean_ctor_get(v_b_631_, 1);
lean_inc(v_snd_646_);
v_snd_647_ = lean_ctor_get(v_snd_646_, 1);
lean_inc(v_snd_647_);
v_fst_648_ = lean_ctor_get(v_b_631_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_b_631_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v_b_631_, 1);
lean_dec(v_unused_991_);
v___x_650_ = v_b_631_;
v_isShared_651_ = v_isSharedCheck_990_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_fst_648_);
lean_dec(v_b_631_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_990_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v_fst_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_988_; 
v_fst_652_ = lean_ctor_get(v_snd_646_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v_snd_646_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v_snd_646_, 1);
lean_dec(v_unused_989_);
v___x_654_ = v_snd_646_;
v_isShared_655_ = v_isSharedCheck_988_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_fst_652_);
lean_dec(v_snd_646_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_988_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_fst_656_; lean_object* v_snd_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_987_; 
v_fst_656_ = lean_ctor_get(v_snd_647_, 0);
v_snd_657_ = lean_ctor_get(v_snd_647_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_snd_647_);
if (v_isSharedCheck_987_ == 0)
{
v___x_659_ = v_snd_647_;
v_isShared_660_ = v_isSharedCheck_987_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snd_657_);
lean_inc(v_fst_656_);
lean_dec(v_snd_647_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_987_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_toConstantVal_661_; lean_object* v_numParams_662_; lean_object* v_lctx_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_toConstantVal_661_ = lean_ctor_get(v_indVal_625_, 0);
lean_inc_ref(v_toConstantVal_661_);
v_numParams_662_ = lean_ctor_get(v_indVal_625_, 1);
v_lctx_663_ = lean_ctor_get(v___y_634_, 2);
v___x_664_ = l_Lean_instInhabitedExpr;
v___x_665_ = lean_nat_add(v_numParams_662_, v___x_626_);
v___x_666_ = lean_nat_sub(v___x_665_, v_a_630_);
lean_dec(v___x_665_);
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_nat_sub(v___x_666_, v___x_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_array_get_borrowed(v___x_664_, v_xs_627_, v___x_668_);
lean_inc(v___x_669_);
lean_inc_ref(v_lctx_663_);
v___x_670_ = l_Lean_Meta_occursOrInType(v_lctx_663_, v___x_669_, v_a_628_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1));
v___x_672_ = l_Lean_Core_mkFreshUserName(v___x_671_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__3));
v___x_675_ = l_Lean_Core_mkFreshUserName(v___x_674_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc(v___x_669_);
v___x_677_ = lean_infer_type(v___x_669_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_679_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc_n(v_a_678_, 2);
lean_dec_ref_known(v___x_677_, 1);
v___x_679_ = l_Lean_Meta_isProp(v_a_678_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v_a_686_; uint8_t v___x_739_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = l_Lean_mkIdent(v_a_673_);
v___x_682_ = l_Lean_mkIdent(v_a_676_);
lean_inc(v___x_681_);
v___x_683_ = lean_array_push(v_fst_648_, v___x_681_);
lean_inc(v___x_682_);
v___x_684_ = lean_array_push(v_fst_652_, v___x_682_);
v___x_739_ = lean_unbox(v_a_680_);
if (v___x_739_ == 0)
{
lean_object* v_name_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_910_; 
v_name_740_ = lean_ctor_get(v_toConstantVal_661_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_toConstantVal_661_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; lean_object* v_unused_912_; 
v_unused_911_ = lean_ctor_get(v_toConstantVal_661_, 2);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_toConstantVal_661_, 1);
lean_dec(v_unused_912_);
v___x_742_ = v_toConstantVal_661_;
v_isShared_743_ = v_isSharedCheck_910_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_name_740_);
lean_dec(v_toConstantVal_661_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_910_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
uint8_t v___x_744_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v_lower_856_; lean_object* v_upper_857_; 
v___x_744_ = l_Lean_Expr_isAppOf(v_a_678_, v_name_740_);
lean_dec(v_name_740_);
lean_dec(v_a_678_);
if (v___x_744_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
lean_dec(v_a_680_);
v___x_865_ = lean_nat_add(v___x_668_, v___x_667_);
lean_dec(v___x_668_);
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = lean_array_get_size(v_xs_627_);
v___x_868_ = lean_nat_dec_le(v___x_865_, v___x_866_);
if (v___x_868_ == 0)
{
v_lower_856_ = v___x_865_;
v_upper_857_ = v___x_867_;
goto v___jp_855_;
}
else
{
lean_dec(v___x_865_);
v_lower_856_ = v___x_866_;
v_upper_857_ = v___x_867_;
goto v___jp_855_;
}
}
else
{
uint8_t v___x_869_; 
lean_del_object(v___x_742_);
lean_dec(v___x_668_);
lean_del_object(v___x_659_);
lean_del_object(v___x_654_);
lean_del_object(v___x_650_);
v___x_869_ = lean_unbox(v_snd_657_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
lean_dec(v_a_680_);
v___x_870_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc_n(v_a_871_, 4);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_873_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_629_);
v___x_874_ = l_Lean_mkIdent(v_auxFunName_629_);
v___x_875_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_876_ = l_Lean_Syntax_node2(v_a_871_, v___x_875_, v___x_681_, v___x_682_);
v___x_877_ = l_Lean_Syntax_node2(v_a_871_, v___x_873_, v___x_874_, v___x_876_);
v___x_878_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_879_, 0, v_a_871_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Lean_Syntax_node3(v_a_871_, v___x_872_, v___x_877_, v___x_879_, v_fst_656_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_snd_657_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_684_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_683_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v_a_640_ = v___x_883_;
goto v___jp_639_;
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v___x_684_);
lean_dec_ref(v___x_683_);
lean_dec(v___x_682_);
lean_dec(v___x_681_);
lean_dec(v_snd_657_);
lean_dec(v_fst_656_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_884_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_870_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_870_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v___x_892_; 
lean_dec(v_snd_657_);
lean_dec(v_fst_656_);
v___x_892_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc_n(v_a_893_, 2);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_629_);
v___x_895_ = l_Lean_mkIdent(v_auxFunName_629_);
v___x_896_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_897_ = l_Lean_Syntax_node2(v_a_893_, v___x_896_, v___x_681_, v___x_682_);
v___x_898_ = l_Lean_Syntax_node2(v_a_893_, v___x_894_, v___x_895_, v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v_a_680_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_684_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_683_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v_a_640_ = v___x_901_;
goto v___jp_639_;
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v___x_684_);
lean_dec_ref(v___x_683_);
lean_dec(v___x_682_);
lean_dec(v___x_681_);
lean_dec(v_a_680_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_902_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_892_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_892_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
v___jp_745_:
{
uint8_t v___x_749_; 
v___x_749_ = lean_nat_dec_lt(v___y_746_, v___y_748_);
if (v___x_749_ == 0)
{
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_del_object(v___x_742_);
v_a_686_ = v___x_749_;
goto v___jp_685_;
}
else
{
size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v___x_750_ = lean_usize_of_nat(v___y_746_);
lean_dec(v___y_746_);
v___x_751_ = lean_usize_of_nat(v___y_748_);
lean_dec(v___y_748_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_669_, v___y_747_, v___x_750_, v___x_751_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec_ref(v___y_747_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; uint8_t v___x_754_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = lean_unbox(v_a_753_);
if (v___x_754_ == 0)
{
uint8_t v___x_755_; 
lean_del_object(v___x_742_);
v___x_755_ = lean_unbox(v_a_753_);
lean_dec(v_a_753_);
v_a_686_ = v___x_755_;
goto v___jp_685_;
}
else
{
lean_object* v___x_756_; 
lean_dec(v_a_753_);
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_del_object(v___x_654_);
lean_del_object(v___x_650_);
v___x_756_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_toCold_757_; lean_object* v_a_758_; lean_object* v_quotContext_759_; lean_object* v_currMacroScope_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v_toCold_757_ = lean_ctor_get(v___y_636_, 0);
v_a_758_ = lean_ctor_get(v___x_756_, 0);
lean_inc_n(v_a_758_, 11);
lean_dec_ref_known(v___x_756_, 1);
v_quotContext_759_ = lean_ctor_get(v_toCold_757_, 8);
v_currMacroScope_760_ = lean_ctor_get(v_toCold_757_, 9);
v___x_761_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11));
v___x_762_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12));
v___x_763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_763_, 0, v_a_758_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14));
v___x_765_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_766_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
lean_inc(v_currMacroScope_760_);
lean_inc(v_quotContext_759_);
v___x_767_ = l_Lean_addMacroScope(v_quotContext_759_, v___x_766_, v_currMacroScope_760_);
v___x_768_ = lean_box(0);
v___x_769_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_769_, 0, v_a_758_);
lean_ctor_set(v___x_769_, 1, v___x_765_);
lean_ctor_set(v___x_769_, 2, v___x_767_);
lean_ctor_set(v___x_769_, 3, v___x_768_);
lean_inc_ref(v___x_769_);
v___x_770_ = l_Lean_Syntax_node1(v_a_758_, v___x_764_, v___x_769_);
v___x_771_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_772_, 0, v_a_758_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_774_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_775_, 0, v_a_758_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = l_Lean_Syntax_node3(v_a_758_, v___x_773_, v___x_681_, v___x_775_, v___x_682_);
v___x_777_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19));
v___x_778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_778_, 0, v_a_758_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21));
v___x_780_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22));
v___x_781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_781_, 0, v_a_758_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25));
v___x_783_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27));
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_785_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28));
v___x_786_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29));
v___x_787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_787_, 0, v_a_758_);
lean_ctor_set(v___x_787_, 1, v___x_785_);
v___x_788_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31));
v___x_789_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 1);
lean_ctor_set(v___x_742_, 2, v___x_789_);
lean_ctor_set(v___x_742_, 1, v___x_784_);
lean_ctor_set(v___x_742_, 0, v_a_758_);
v___x_791_ = v___x_742_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_758_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v___x_789_);
v___x_791_ = v_reuseFailAlloc_838_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_792_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_793_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_794_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
lean_inc_n(v_a_758_, 20);
v___x_795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_795_, 0, v_a_758_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_797_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_798_ = lean_box(0);
lean_inc_n(v_currMacroScope_760_, 3);
lean_inc_n(v_quotContext_759_, 3);
v___x_799_ = l_Lean_addMacroScope(v_quotContext_759_, v___x_798_, v_currMacroScope_760_);
v___x_800_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50));
v___x_801_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_801_, 0, v_a_758_);
lean_ctor_set(v___x_801_, 1, v___x_797_);
lean_ctor_set(v___x_801_, 2, v___x_799_);
lean_ctor_set(v___x_801_, 3, v___x_800_);
v___x_802_ = l_Lean_Syntax_node1(v_a_758_, v___x_796_, v___x_801_);
v___x_803_ = l_Lean_Syntax_node2(v_a_758_, v___x_793_, v___x_795_, v___x_802_);
v___x_804_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_805_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54);
v___x_806_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55));
v___x_807_ = l_Lean_addMacroScope(v_quotContext_759_, v___x_806_, v_currMacroScope_760_);
v___x_808_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59));
v___x_809_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_809_, 0, v_a_758_);
lean_ctor_set(v___x_809_, 1, v___x_805_);
lean_ctor_set(v___x_809_, 2, v___x_807_);
lean_ctor_set(v___x_809_, 3, v___x_808_);
v___x_810_ = l_Lean_Syntax_node1(v_a_758_, v___x_784_, v___x_769_);
v___x_811_ = l_Lean_Syntax_node2(v_a_758_, v___x_804_, v___x_809_, v___x_810_);
v___x_812_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_813_, 0, v_a_758_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Lean_Syntax_node3(v_a_758_, v___x_792_, v___x_803_, v___x_811_, v___x_813_);
lean_inc_ref_n(v___x_791_, 3);
v___x_815_ = l_Lean_Syntax_node2(v_a_758_, v___x_788_, v___x_791_, v___x_814_);
v___x_816_ = l_Lean_Syntax_node1(v_a_758_, v___x_784_, v___x_815_);
v___x_817_ = l_Lean_Syntax_node4(v_a_758_, v___x_786_, v___x_787_, v___x_816_, v___x_791_, v___x_791_);
v___x_818_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61));
v___x_819_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62));
v___x_820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_820_, 0, v_a_758_);
lean_ctor_set(v___x_820_, 1, v___x_818_);
v___x_821_ = l_Lean_Syntax_node2(v_a_758_, v___x_819_, v___x_820_, v_fst_656_);
v___x_822_ = l_Lean_Syntax_node3(v_a_758_, v___x_784_, v___x_817_, v___x_791_, v___x_821_);
v___x_823_ = l_Lean_Syntax_node1(v_a_758_, v___x_783_, v___x_822_);
v___x_824_ = l_Lean_Syntax_node1(v_a_758_, v___x_782_, v___x_823_);
v___x_825_ = l_Lean_Syntax_node2(v_a_758_, v___x_779_, v___x_781_, v___x_824_);
v___x_826_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63));
v___x_827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_827_, 0, v_a_758_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_829_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_830_ = l_Lean_addMacroScope(v_quotContext_759_, v___x_829_, v_currMacroScope_760_);
v___x_831_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65));
v___x_832_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_832_, 0, v_a_758_);
lean_ctor_set(v___x_832_, 1, v___x_828_);
lean_ctor_set(v___x_832_, 2, v___x_830_);
lean_ctor_set(v___x_832_, 3, v___x_831_);
v___x_833_ = l_Lean_Syntax_node8(v_a_758_, v___x_761_, v___x_763_, v___x_770_, v___x_772_, v___x_776_, v___x_778_, v___x_825_, v___x_827_, v___x_832_);
v___x_834_ = lean_box(v___x_744_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_684_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_683_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v_a_640_ = v___x_837_;
goto v___jp_639_;
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_del_object(v___x_742_);
lean_dec_ref(v___x_684_);
lean_dec_ref(v___x_683_);
lean_dec(v___x_682_);
lean_dec(v___x_681_);
lean_dec(v_fst_656_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_839_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_756_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_756_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_del_object(v___x_742_);
lean_dec_ref(v___x_684_);
lean_dec_ref(v___x_683_);
lean_dec(v___x_682_);
lean_dec(v___x_681_);
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_fst_656_);
lean_del_object(v___x_654_);
lean_del_object(v___x_650_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_847_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_752_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_752_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
v___jp_855_:
{
lean_object* v___x_858_; lean_object* v_array_859_; lean_object* v_start_860_; lean_object* v_stop_861_; uint8_t v___x_862_; 
lean_inc_ref(v_xs_627_);
v___x_858_ = l_Array_toSubarray___redArg(v_xs_627_, v_lower_856_, v_upper_857_);
v_array_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc_ref(v_array_859_);
v_start_860_ = lean_ctor_get(v___x_858_, 1);
lean_inc(v_start_860_);
v_stop_861_ = lean_ctor_get(v___x_858_, 2);
lean_inc(v_stop_861_);
lean_dec_ref(v___x_858_);
v___x_862_ = lean_nat_dec_lt(v_start_860_, v_stop_861_);
if (v___x_862_ == 0)
{
lean_dec(v_stop_861_);
lean_dec(v_start_860_);
lean_dec_ref(v_array_859_);
lean_del_object(v___x_742_);
v_a_686_ = v___x_862_;
goto v___jp_685_;
}
else
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = lean_array_get_size(v_array_859_);
v___x_864_ = lean_nat_dec_le(v_stop_861_, v___x_863_);
if (v___x_864_ == 0)
{
lean_dec(v_stop_861_);
v___y_746_ = v_start_860_;
v___y_747_ = v_array_859_;
v___y_748_ = v___x_863_;
goto v___jp_745_;
}
else
{
v___y_746_ = v_start_860_;
v___y_747_ = v_array_859_;
v___y_748_ = v_stop_861_;
goto v___jp_745_;
}
}
}
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec(v___x_682_);
lean_dec(v___x_681_);
lean_dec(v_a_680_);
lean_dec(v_a_678_);
lean_dec(v___x_668_);
lean_dec_ref(v_toConstantVal_661_);
lean_del_object(v___x_659_);
lean_del_object(v___x_654_);
lean_del_object(v___x_650_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_fst_656_);
lean_ctor_set(v___x_913_, 1, v_snd_657_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_684_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_683_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v_a_640_ = v___x_915_;
goto v___jp_639_;
}
v___jp_685_:
{
uint8_t v___x_687_; 
v___x_687_ = lean_unbox(v_snd_657_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
v___x_688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc_n(v_a_689_, 4);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_691_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_692_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_693_, 0, v_a_689_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_Syntax_node3(v_a_689_, v___x_691_, v___x_681_, v___x_693_, v___x_682_);
v___x_695_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_696_, 0, v_a_689_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Lean_Syntax_node3(v_a_689_, v___x_690_, v___x_694_, v___x_696_, v_fst_656_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_697_);
v___x_699_ = v___x_659_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_snd_657_);
v___x_699_ = v_reuseFailAlloc_706_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_699_);
lean_ctor_set(v___x_654_, 0, v___x_684_);
v___x_701_ = v___x_654_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_699_);
v___x_701_ = v_reuseFailAlloc_705_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_703_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___x_701_);
lean_ctor_set(v___x_650_, 0, v___x_683_);
v___x_703_ = v___x_650_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v_a_640_ = v___x_703_;
goto v___jp_639_;
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v___x_684_);
lean_dec_ref(v___x_683_);
lean_dec(v___x_682_);
lean_dec(v___x_681_);
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_fst_656_);
lean_del_object(v___x_654_);
lean_del_object(v___x_650_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_707_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_688_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_688_);
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
else
{
lean_object* v___x_715_; 
lean_dec(v_snd_657_);
lean_dec(v_fst_656_);
v___x_715_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc_n(v_a_716_, 2);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_718_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_719_, 0, v_a_716_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = l_Lean_Syntax_node3(v_a_716_, v___x_717_, v___x_681_, v___x_719_, v___x_682_);
v___x_721_ = lean_box(v_a_686_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_721_);
lean_ctor_set(v___x_659_, 0, v___x_720_);
v___x_723_ = v___x_659_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_730_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_723_);
lean_ctor_set(v___x_654_, 0, v___x_684_);
v___x_725_ = v___x_654_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_729_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___x_725_);
lean_ctor_set(v___x_650_, 0, v___x_683_);
v___x_727_ = v___x_650_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
v_a_640_ = v___x_727_;
goto v___jp_639_;
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v___x_684_);
lean_dec_ref(v___x_683_);
lean_dec(v___x_682_);
lean_dec(v___x_681_);
lean_del_object(v___x_659_);
lean_del_object(v___x_654_);
lean_del_object(v___x_650_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_731_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_715_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_715_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_a_678_);
lean_dec(v_a_676_);
lean_dec(v_a_673_);
lean_dec(v___x_668_);
lean_dec_ref(v_toConstantVal_661_);
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_fst_656_);
lean_del_object(v___x_654_);
lean_dec(v_fst_652_);
lean_del_object(v___x_650_);
lean_dec(v_fst_648_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_916_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_679_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_679_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_a_676_);
lean_dec(v_a_673_);
lean_dec(v___x_668_);
lean_dec_ref(v_toConstantVal_661_);
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_fst_656_);
lean_del_object(v___x_654_);
lean_dec(v_fst_652_);
lean_del_object(v___x_650_);
lean_dec(v_fst_648_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_924_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_677_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_677_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v_a_673_);
lean_dec(v___x_668_);
lean_dec_ref(v_toConstantVal_661_);
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_fst_656_);
lean_del_object(v___x_654_);
lean_dec(v_fst_652_);
lean_del_object(v___x_650_);
lean_dec(v_fst_648_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_932_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_675_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_675_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
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
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v___x_668_);
lean_dec_ref(v_toConstantVal_661_);
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_fst_656_);
lean_del_object(v___x_654_);
lean_dec(v_fst_652_);
lean_del_object(v___x_650_);
lean_dec(v_fst_648_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_940_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_672_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_672_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v___x_668_);
lean_dec_ref(v_toConstantVal_661_);
v___x_948_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__1));
v___x_949_ = l_Lean_Core_mkFreshUserName(v___x_948_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc_n(v_a_952_, 3);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = l_Lean_mkIdent(v_a_950_);
lean_inc(v___x_953_);
v___x_954_ = lean_array_push(v_fst_648_, v___x_953_);
v___x_955_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__67));
v___x_956_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__68));
v___x_957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_957_, 0, v_a_952_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v_a_952_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Lean_Syntax_node3(v_a_952_, v___x_955_, v___x_957_, v___x_953_, v___x_959_);
v___x_961_ = lean_array_push(v_fst_652_, v___x_960_);
if (v_isShared_660_ == 0)
{
v___x_963_ = v___x_659_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_fst_656_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_snd_657_);
v___x_963_ = v_reuseFailAlloc_970_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_965_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_963_);
lean_ctor_set(v___x_654_, 0, v___x_961_);
v___x_965_ = v___x_654_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_963_);
v___x_965_ = v_reuseFailAlloc_969_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_967_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___x_965_);
lean_ctor_set(v___x_650_, 0, v___x_954_);
v___x_967_ = v___x_650_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
v_a_640_ = v___x_967_;
goto v___jp_639_;
}
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v_a_950_);
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_fst_656_);
lean_del_object(v___x_654_);
lean_dec(v_fst_652_);
lean_del_object(v___x_650_);
lean_dec(v_fst_648_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_971_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_951_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_951_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_fst_656_);
lean_del_object(v___x_654_);
lean_dec(v_fst_652_);
lean_del_object(v___x_650_);
lean_dec(v_fst_648_);
lean_dec(v_a_630_);
lean_dec(v_auxFunName_629_);
lean_dec_ref(v_xs_627_);
lean_dec_ref(v_indVal_625_);
v_a_979_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_949_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_949_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_992_, lean_object* v_indVal_993_, lean_object* v___x_994_, lean_object* v_xs_995_, lean_object* v_a_996_, lean_object* v_auxFunName_997_, lean_object* v_a_998_, lean_object* v_b_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_992_, v_indVal_993_, v___x_994_, v_xs_995_, v_a_996_, v_auxFunName_997_, v_a_998_, v_b_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec_ref(v_a_996_);
lean_dec(v___x_994_);
lean_dec(v_upperBound_992_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(lean_object* v_upperBound_1008_, lean_object* v_a_1009_, lean_object* v_b_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_nat_dec_lt(v_a_1009_, v_upperBound_1008_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; 
lean_dec(v_a_1009_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_b_1010_);
return v___x_1019_;
}
else
{
lean_object* v___x_1020_; 
v___x_1020_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v_fst_1024_; lean_object* v_snd_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1043_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v_fst_1024_ = lean_ctor_get(v_b_1010_, 0);
v_snd_1025_ = lean_ctor_get(v_b_1010_, 1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_b_1010_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1027_ = v_b_1010_;
v_isShared_1028_ = v_isSharedCheck_1043_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_snd_1025_);
lean_inc(v_fst_1024_);
lean_dec(v_b_1010_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1043_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1029_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
lean_inc(v_a_1021_);
v___x_1030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_a_1021_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_1032_ = l_Lean_Syntax_node1(v_a_1021_, v___x_1031_, v___x_1030_);
v___x_1033_ = lean_array_push(v_fst_1024_, v___x_1032_);
lean_inc(v_a_1023_);
v___x_1034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_a_1023_);
lean_ctor_set(v___x_1034_, 1, v___x_1029_);
v___x_1035_ = l_Lean_Syntax_node1(v_a_1023_, v___x_1031_, v___x_1034_);
v___x_1036_ = lean_array_push(v_snd_1025_, v___x_1035_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 1, v___x_1036_);
lean_ctor_set(v___x_1027_, 0, v___x_1033_);
v___x_1038_ = v___x_1027_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_nat_add(v_a_1009_, v___x_1039_);
lean_dec(v_a_1009_);
v_a_1009_ = v___x_1040_;
v_b_1010_ = v___x_1038_;
goto _start;
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v_a_1021_);
lean_dec_ref(v_b_1010_);
lean_dec(v_a_1009_);
v_a_1044_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1022_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1022_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v_b_1010_);
lean_dec(v_a_1009_);
v_a_1052_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1020_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1020_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___boxed(lean_object* v_upperBound_1060_, lean_object* v_a_1061_, lean_object* v_b_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_upperBound_1060_, v_a_1061_, v_b_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v_upperBound_1060_);
return v_res_1070_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0));
v___x_1073_ = l_String_toRawSubstring_x27(v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1(lean_object* v_indVal_1092_, lean_object* v___x_1093_, lean_object* v_alts_1094_, lean_object* v_numFields_1095_, lean_object* v_auxFunName_1096_, lean_object* v___f_1097_, lean_object* v_head_1098_, lean_object* v_xs_1099_, lean_object* v_type_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_Core_betaReduce(v_type_1100_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v_numParams_1110_; lean_object* v_numIndices_1111_; lean_object* v___x_1112_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 1);
v_numParams_1110_ = lean_ctor_get(v_indVal_1092_, 1);
lean_inc(v_numParams_1110_);
v_numIndices_1111_ = lean_ctor_get(v_indVal_1092_, 2);
lean_inc_ref(v_alts_1094_);
lean_inc(v___x_1093_);
v___x_1112_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg(v_numIndices_1111_, v___x_1093_, v_alts_1094_, v___y_1105_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_toCold_1113_; lean_object* v_a_1114_; lean_object* v_ref_1115_; lean_object* v_quotContext_1116_; lean_object* v_currMacroScope_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_toCold_1113_ = lean_ctor_get(v___y_1105_, 0);
v_a_1114_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1112_, 1);
v_ref_1115_ = lean_ctor_get(v___y_1105_, 2);
v_quotContext_1116_ = lean_ctor_get(v_toCold_1113_, 8);
v_currMacroScope_1117_ = lean_ctor_get(v_toCold_1113_, 9);
v___x_1118_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1);
v___x_1119_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2));
v___x_1120_ = 0;
v___x_1121_ = l_Lean_SourceInfo_fromRef(v_ref_1115_, v___x_1120_);
lean_inc(v_currMacroScope_1117_);
lean_inc(v_quotContext_1116_);
v___x_1122_ = l_Lean_addMacroScope(v_quotContext_1116_, v___x_1119_, v_currMacroScope_1117_);
v___x_1123_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5));
v___x_1124_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1121_);
lean_ctor_set(v___x_1124_, 1, v___x_1118_);
lean_ctor_set(v___x_1124_, 2, v___x_1122_);
lean_ctor_set(v___x_1124_, 3, v___x_1123_);
v___x_1125_ = 1;
v___x_1126_ = lean_box(v___x_1125_);
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1124_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
lean_inc_ref(v_alts_1094_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_alts_1094_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_alts_1094_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
lean_inc(v___x_1093_);
v___x_1130_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_numFields_1095_, v_indVal_1092_, v_numFields_1095_, v_xs_1099_, v_a_1109_, v_auxFunName_1096_, v___x_1093_, v___x_1129_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v_a_1109_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v_snd_1132_; lean_object* v_snd_1133_; lean_object* v_fst_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1246_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v_snd_1132_ = lean_ctor_get(v_a_1131_, 1);
lean_inc(v_snd_1132_);
v_snd_1133_ = lean_ctor_get(v_snd_1132_, 1);
lean_inc(v_snd_1133_);
v_fst_1134_ = lean_ctor_get(v_a_1131_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_a_1131_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v_a_1131_, 1);
lean_dec(v_unused_1247_);
v___x_1136_ = v_a_1131_;
v_isShared_1137_ = v_isSharedCheck_1246_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_fst_1134_);
lean_dec(v_a_1131_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1246_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_fst_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1244_; 
v_fst_1138_ = lean_ctor_get(v_snd_1132_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_snd_1132_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v_snd_1132_, 1);
lean_dec(v_unused_1245_);
v___x_1140_ = v_snd_1132_;
v_isShared_1141_ = v_isSharedCheck_1244_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_fst_1138_);
lean_dec(v_snd_1132_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1244_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_fst_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1242_; 
v_fst_1142_ = lean_ctor_get(v_snd_1133_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_snd_1133_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v_snd_1133_, 1);
lean_dec(v_unused_1243_);
v___x_1144_ = v_snd_1133_;
v_isShared_1145_ = v_isSharedCheck_1242_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_fst_1142_);
lean_dec(v_snd_1133_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1242_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_fst_1138_);
lean_ctor_set(v___x_1144_, 0, v_fst_1134_);
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_fst_1134_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_fst_1138_);
v___x_1147_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_numParams_1110_, v___x_1093_, v___x_1147_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v_numParams_1110_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1150_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___x_1148_, 1);
lean_inc_ref(v___f_1097_);
lean_inc(v___y_1106_);
lean_inc_ref(v___y_1105_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc(v___y_1102_);
lean_inc_ref(v___y_1101_);
v___x_1150_ = lean_apply_7(v___f_1097_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, lean_box(0));
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
lean_inc_ref(v___f_1097_);
lean_inc(v___y_1106_);
lean_inc_ref(v___y_1105_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc(v___y_1102_);
lean_inc_ref(v___y_1101_);
v___x_1152_ = lean_apply_7(v___f_1097_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, lean_box(0));
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1154_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
lean_inc(v___y_1106_);
lean_inc_ref(v___y_1105_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc(v___y_1102_);
lean_inc_ref(v___y_1101_);
v___x_1154_ = lean_apply_7(v___f_1097_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, lean_box(0));
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1208_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1208_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1208_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_fst_1159_; lean_object* v_snd_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1207_; 
v_fst_1159_ = lean_ctor_get(v_a_1149_, 0);
v_snd_1160_ = lean_ctor_get(v_a_1149_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_a_1149_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1162_ = v_a_1149_;
v_isShared_1163_ = v_isSharedCheck_1207_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_snd_1160_);
lean_inc(v_fst_1159_);
lean_dec(v_a_1149_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1207_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1164_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_1165_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6));
lean_inc(v_a_1151_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set_tag(v___x_1162_, 2);
lean_ctor_set(v___x_1162_, 1, v___x_1165_);
lean_ctor_set(v___x_1162_, 0, v_a_1151_);
v___x_1167_ = v___x_1162_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1151_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = l_Lean_mkIdent(v_head_1098_);
lean_inc(v_a_1153_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 2);
lean_ctor_set(v___x_1140_, 1, v___x_1165_);
lean_ctor_set(v___x_1140_, 0, v_a_1153_);
v___x_1170_ = v___x_1140_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1153_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1165_);
v___x_1170_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1171_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8));
lean_inc(v___x_1168_);
lean_inc_n(v_a_1151_, 2);
v___x_1172_ = l_Lean_Syntax_node2(v_a_1151_, v___x_1171_, v___x_1167_, v___x_1168_);
lean_inc_n(v_a_1153_, 2);
v___x_1173_ = l_Lean_Syntax_node2(v_a_1153_, v___x_1171_, v___x_1170_, v___x_1168_);
v___x_1174_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_1175_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_1176_ = l_Array_reverse___redArg(v_fst_1159_);
v___x_1177_ = l_Array_append___redArg(v___x_1175_, v___x_1176_);
lean_dec_ref(v___x_1176_);
v___x_1178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1178_, 0, v_a_1151_);
lean_ctor_set(v___x_1178_, 1, v___x_1174_);
lean_ctor_set(v___x_1178_, 2, v___x_1177_);
v___x_1179_ = l_Array_reverse___redArg(v_snd_1160_);
v___x_1180_ = l_Array_append___redArg(v___x_1175_, v___x_1179_);
lean_dec_ref(v___x_1179_);
v___x_1181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1181_, 0, v_a_1153_);
lean_ctor_set(v___x_1181_, 1, v___x_1174_);
lean_ctor_set(v___x_1181_, 2, v___x_1180_);
v___x_1182_ = l_Lean_Syntax_node2(v_a_1151_, v___x_1164_, v___x_1172_, v___x_1178_);
v___x_1183_ = lean_array_push(v_a_1114_, v___x_1182_);
v___x_1184_ = l_Lean_Syntax_node2(v_a_1153_, v___x_1164_, v___x_1173_, v___x_1181_);
v___x_1185_ = lean_array_push(v___x_1183_, v___x_1184_);
v___x_1186_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_1187_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
lean_inc(v_a_1155_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 2);
lean_ctor_set(v___x_1136_, 1, v___x_1187_);
lean_ctor_set(v___x_1136_, 0, v_a_1155_);
v___x_1189_ = v___x_1136_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1155_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
size_t v_sz_1190_; size_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v_sz_1190_ = lean_array_size(v___x_1185_);
v___x_1191_ = ((size_t)0ULL);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_1190_, v___x_1191_, v___x_1185_);
v___x_1193_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_1194_ = l_Lean_mkSepArray(v___x_1192_, v___x_1193_);
lean_dec_ref(v___x_1192_);
v___x_1195_ = l_Array_append___redArg(v___x_1175_, v___x_1194_);
lean_dec_ref(v___x_1194_);
lean_inc_n(v_a_1155_, 3);
v___x_1196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1196_, 0, v_a_1155_);
lean_ctor_set(v___x_1196_, 1, v___x_1174_);
lean_ctor_set(v___x_1196_, 2, v___x_1195_);
v___x_1197_ = l_Lean_Syntax_node1(v_a_1155_, v___x_1174_, v___x_1196_);
v___x_1198_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_1199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1199_, 0, v_a_1155_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_Syntax_node4(v_a_1155_, v___x_1186_, v___x_1189_, v___x_1197_, v___x_1199_, v_fst_1142_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1200_);
v___x_1202_ = v___x_1157_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v_a_1153_);
lean_dec(v_a_1151_);
lean_dec(v_a_1149_);
lean_dec(v_fst_1142_);
lean_del_object(v___x_1140_);
lean_del_object(v___x_1136_);
lean_dec(v_a_1114_);
lean_dec(v_head_1098_);
v_a_1209_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1154_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1154_);
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
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_a_1151_);
lean_dec(v_a_1149_);
lean_dec(v_fst_1142_);
lean_del_object(v___x_1140_);
lean_del_object(v___x_1136_);
lean_dec(v_a_1114_);
lean_dec(v_head_1098_);
lean_dec_ref(v___f_1097_);
v_a_1217_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1152_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1152_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_a_1149_);
lean_dec(v_fst_1142_);
lean_del_object(v___x_1140_);
lean_del_object(v___x_1136_);
lean_dec(v_a_1114_);
lean_dec(v_head_1098_);
lean_dec_ref(v___f_1097_);
v_a_1225_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1150_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1150_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_fst_1142_);
lean_del_object(v___x_1140_);
lean_del_object(v___x_1136_);
lean_dec(v_a_1114_);
lean_dec(v_head_1098_);
lean_dec_ref(v___f_1097_);
v_a_1233_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1148_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1148_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
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
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v_a_1114_);
lean_dec(v_numParams_1110_);
lean_dec(v_head_1098_);
lean_dec_ref(v___f_1097_);
lean_dec(v___x_1093_);
v_a_1248_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1130_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1130_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_numParams_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_xs_1099_);
lean_dec(v_head_1098_);
lean_dec_ref(v___f_1097_);
lean_dec(v_auxFunName_1096_);
lean_dec_ref(v_alts_1094_);
lean_dec(v___x_1093_);
lean_dec_ref(v_indVal_1092_);
v_a_1256_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1112_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1112_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_xs_1099_);
lean_dec(v_head_1098_);
lean_dec_ref(v___f_1097_);
lean_dec(v_auxFunName_1096_);
lean_dec_ref(v_alts_1094_);
lean_dec(v___x_1093_);
lean_dec_ref(v_indVal_1092_);
v_a_1264_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1108_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1108_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___boxed(lean_object* v_indVal_1272_, lean_object* v___x_1273_, lean_object* v_alts_1274_, lean_object* v_numFields_1275_, lean_object* v_auxFunName_1276_, lean_object* v___f_1277_, lean_object* v_head_1278_, lean_object* v_xs_1279_, lean_object* v_type_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1(v_indVal_1272_, v___x_1273_, v_alts_1274_, v_numFields_1275_, v_auxFunName_1276_, v___f_1277_, v_head_1278_, v_xs_1279_, v_type_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v_numFields_1275_);
return v_res_1288_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_instMonadEIO(lean_box(0));
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(lean_object* v_msg_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v_toApplicative_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1397_; 
v___x_1304_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__0);
v___x_1305_ = l_StateRefT_x27_instMonad___redArg(v___x_1304_);
v_toApplicative_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___x_1305_, 1);
lean_dec(v_unused_1398_);
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1397_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_toApplicative_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1397_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_toFunctor_1310_; lean_object* v_toSeq_1311_; lean_object* v_toSeqLeft_1312_; lean_object* v_toSeqRight_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1395_; 
v_toFunctor_1310_ = lean_ctor_get(v_toApplicative_1306_, 0);
v_toSeq_1311_ = lean_ctor_get(v_toApplicative_1306_, 2);
v_toSeqLeft_1312_ = lean_ctor_get(v_toApplicative_1306_, 3);
v_toSeqRight_1313_ = lean_ctor_get(v_toApplicative_1306_, 4);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_toApplicative_1306_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; 
v_unused_1396_ = lean_ctor_get(v_toApplicative_1306_, 1);
lean_dec(v_unused_1396_);
v___x_1315_ = v_toApplicative_1306_;
v_isShared_1316_ = v_isSharedCheck_1395_;
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
v_isShared_1316_ = v_isSharedCheck_1395_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___f_1317_; lean_object* v___f_1318_; lean_object* v___f_1319_; lean_object* v___f_1320_; lean_object* v___x_1321_; lean_object* v___f_1322_; lean_object* v___f_1323_; lean_object* v___f_1324_; lean_object* v___x_1326_; 
v___f_1317_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__1));
v___f_1318_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__2));
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
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___f_1317_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v___f_1324_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v___f_1323_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v___f_1322_);
v___x_1326_ = v_reuseFailAlloc_1394_;
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
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___f_1318_);
v___x_1328_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v_toApplicative_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1391_; 
v___x_1329_ = l_StateRefT_x27_instMonad___redArg(v___x_1328_);
v_toApplicative_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; 
v_unused_1392_ = lean_ctor_get(v___x_1329_, 1);
lean_dec(v_unused_1392_);
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1391_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_toApplicative_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1391_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v_toFunctor_1334_; lean_object* v_toSeq_1335_; lean_object* v_toSeqLeft_1336_; lean_object* v_toSeqRight_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1389_; 
v_toFunctor_1334_ = lean_ctor_get(v_toApplicative_1330_, 0);
v_toSeq_1335_ = lean_ctor_get(v_toApplicative_1330_, 2);
v_toSeqLeft_1336_ = lean_ctor_get(v_toApplicative_1330_, 3);
v_toSeqRight_1337_ = lean_ctor_get(v_toApplicative_1330_, 4);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_toApplicative_1330_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; 
v_unused_1390_ = lean_ctor_get(v_toApplicative_1330_, 1);
lean_dec(v_unused_1390_);
v___x_1339_ = v_toApplicative_1330_;
v_isShared_1340_ = v_isSharedCheck_1389_;
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
v_isShared_1340_ = v_isSharedCheck_1389_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___f_1341_; lean_object* v___f_1342_; lean_object* v___f_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; lean_object* v___f_1346_; lean_object* v___f_1347_; lean_object* v___f_1348_; lean_object* v___x_1350_; 
v___f_1341_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__3));
v___f_1342_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__4));
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
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___f_1341_);
lean_ctor_set(v_reuseFailAlloc_1388_, 2, v___f_1348_);
lean_ctor_set(v_reuseFailAlloc_1388_, 3, v___f_1347_);
lean_ctor_set(v_reuseFailAlloc_1388_, 4, v___f_1346_);
v___x_1350_ = v_reuseFailAlloc_1388_;
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
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___f_1342_);
v___x_1352_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v_toApplicative_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1385_; 
v___x_1353_ = l_StateRefT_x27_instMonad___redArg(v___x_1352_);
v_toApplicative_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; 
v_unused_1386_ = lean_ctor_get(v___x_1353_, 1);
lean_dec(v_unused_1386_);
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1385_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_toApplicative_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1385_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v_toFunctor_1358_; lean_object* v_toSeq_1359_; lean_object* v_toSeqLeft_1360_; lean_object* v_toSeqRight_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1383_; 
v_toFunctor_1358_ = lean_ctor_get(v_toApplicative_1354_, 0);
v_toSeq_1359_ = lean_ctor_get(v_toApplicative_1354_, 2);
v_toSeqLeft_1360_ = lean_ctor_get(v_toApplicative_1354_, 3);
v_toSeqRight_1361_ = lean_ctor_get(v_toApplicative_1354_, 4);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_toApplicative_1354_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; 
v_unused_1384_ = lean_ctor_get(v_toApplicative_1354_, 1);
lean_dec(v_unused_1384_);
v___x_1363_ = v_toApplicative_1354_;
v_isShared_1364_ = v_isSharedCheck_1383_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_toSeqRight_1361_);
lean_inc(v_toSeqLeft_1360_);
lean_inc(v_toSeq_1359_);
lean_inc(v_toFunctor_1358_);
lean_dec(v_toApplicative_1354_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1383_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___f_1365_; lean_object* v___f_1366_; lean_object* v___f_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; lean_object* v___f_1370_; lean_object* v___f_1371_; lean_object* v___f_1372_; lean_object* v___x_1374_; 
v___f_1365_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__5));
v___f_1366_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1358_);
v___f_1367_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1367_, 0, v_toFunctor_1358_);
v___f_1368_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1368_, 0, v_toFunctor_1358_);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___f_1367_);
lean_ctor_set(v___x_1369_, 1, v___f_1368_);
v___f_1370_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1370_, 0, v_toSeqRight_1361_);
v___f_1371_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1371_, 0, v_toSeqLeft_1360_);
v___f_1372_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1372_, 0, v_toSeq_1359_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 4, v___f_1370_);
lean_ctor_set(v___x_1363_, 3, v___f_1371_);
lean_ctor_set(v___x_1363_, 2, v___f_1372_);
lean_ctor_set(v___x_1363_, 1, v___f_1365_);
lean_ctor_set(v___x_1363_, 0, v___x_1369_);
v___x_1374_ = v___x_1363_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v___f_1365_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v___f_1372_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v___f_1371_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v___f_1370_);
v___x_1374_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1376_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v___f_1366_);
lean_ctor_set(v___x_1356_, 0, v___x_1374_);
v___x_1376_ = v___x_1356_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v___f_1366_);
v___x_1376_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_45134__overap_1379_; lean_object* v___x_1380_; 
v___x_1377_ = lean_box(0);
v___x_1378_ = l_instInhabitedOfMonad___redArg(v___x_1376_, v___x_1377_);
v___x_45134__overap_1379_ = lean_panic_fn_borrowed(v___x_1378_, v_msg_1296_);
lean_dec(v___x_1378_);
lean_inc(v___y_1302_);
lean_inc_ref(v___y_1301_);
lean_inc(v___y_1300_);
lean_inc_ref(v___y_1299_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
v___x_1380_ = lean_apply_7(v___x_45134__overap_1379_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, lean_box(0));
return v___x_1380_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(v_msg_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1407_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(lean_object* v_opts_1408_, lean_object* v_opt_1409_){
_start:
{
lean_object* v_name_1410_; lean_object* v_defValue_1411_; lean_object* v_map_1412_; lean_object* v___x_1413_; 
v_name_1410_ = lean_ctor_get(v_opt_1409_, 0);
v_defValue_1411_ = lean_ctor_get(v_opt_1409_, 1);
v_map_1412_ = lean_ctor_get(v_opts_1408_, 0);
v___x_1413_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1412_, v_name_1410_);
if (lean_obj_tag(v___x_1413_) == 0)
{
uint8_t v___x_1414_; 
v___x_1414_ = lean_unbox(v_defValue_1411_);
return v___x_1414_;
}
else
{
lean_object* v_val_1415_; 
v_val_1415_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_val_1415_);
lean_dec_ref_known(v___x_1413_, 1);
if (lean_obj_tag(v_val_1415_) == 1)
{
uint8_t v_v_1416_; 
v_v_1416_ = lean_ctor_get_uint8(v_val_1415_, 0);
lean_dec_ref_known(v_val_1415_, 0);
return v_v_1416_;
}
else
{
uint8_t v___x_1417_; 
lean_dec(v_val_1415_);
v___x_1417_ = lean_unbox(v_defValue_1411_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_opts_1418_, lean_object* v_opt_1419_){
_start:
{
uint8_t v_res_1420_; lean_object* v_r_1421_; 
v_res_1420_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v_opts_1418_, v_opt_1419_);
lean_dec_ref(v_opt_1419_);
lean_dec_ref(v_opts_1418_);
v_r_1421_ = lean_box(v_res_1420_);
return v_r_1421_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_box(1);
v___x_1423_ = l_Lean_MessageData_ofFormat(v___x_1422_);
return v___x_1423_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2));
v___x_1428_ = l_Lean_MessageData_ofFormat(v___x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_x_1429_, lean_object* v_x_1430_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 0)
{
return v_x_1429_;
}
else
{
lean_object* v_head_1431_; lean_object* v_tail_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1454_; 
v_head_1431_ = lean_ctor_get(v_x_1430_, 0);
v_tail_1432_ = lean_ctor_get(v_x_1430_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_x_1430_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1434_ = v_x_1430_;
v_isShared_1435_ = v_isSharedCheck_1454_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_tail_1432_);
lean_inc(v_head_1431_);
lean_dec(v_x_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1454_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_before_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1452_; 
v_before_1436_ = lean_ctor_get(v_head_1431_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_head_1431_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_head_1431_, 1);
lean_dec(v_unused_1453_);
v___x_1438_ = v_head_1431_;
v_isShared_1439_ = v_isSharedCheck_1452_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_before_1436_);
lean_dec(v_head_1431_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1452_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_1439_ == 0)
{
lean_ctor_set_tag(v___x_1438_, 7);
lean_ctor_set(v___x_1438_, 1, v___x_1440_);
lean_ctor_set(v___x_1438_, 0, v_x_1429_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_x_1429_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3);
if (v_isShared_1435_ == 0)
{
lean_ctor_set_tag(v___x_1434_, 7);
lean_ctor_set(v___x_1434_, 1, v___x_1443_);
lean_ctor_set(v___x_1434_, 0, v___x_1442_);
v___x_1445_ = v___x_1434_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = l_Lean_MessageData_ofSyntax(v_before_1436_);
v___x_1447_ = l_Lean_indentD(v___x_1446_);
v___x_1448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1445_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v_x_1429_ = v___x_1448_;
v_x_1430_ = v_tail_1432_;
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
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_1459_ = l_Lean_MessageData_ofFormat(v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_1460_, lean_object* v_macroStack_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_toCold_1464_; lean_object* v_options_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v_toCold_1464_ = lean_ctor_get(v___y_1462_, 0);
v_options_1465_ = lean_ctor_get(v_toCold_1464_, 2);
v___x_1466_ = l_Lean_Elab_pp_macroStack;
v___x_1467_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v_options_1465_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
lean_dec(v_macroStack_1461_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_msgData_1460_);
return v___x_1468_;
}
else
{
if (lean_obj_tag(v_macroStack_1461_) == 0)
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_msgData_1460_);
return v___x_1469_;
}
else
{
lean_object* v_head_1470_; lean_object* v_after_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1486_; 
v_head_1470_ = lean_ctor_get(v_macroStack_1461_, 0);
lean_inc(v_head_1470_);
v_after_1471_ = lean_ctor_get(v_head_1470_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_head_1470_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v_head_1470_, 0);
lean_dec(v_unused_1487_);
v___x_1473_ = v_head_1470_;
v_isShared_1474_ = v_isSharedCheck_1486_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_after_1471_);
lean_dec(v_head_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1486_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1475_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_1474_ == 0)
{
lean_ctor_set_tag(v___x_1473_, 7);
lean_ctor_set(v___x_1473_, 1, v___x_1475_);
lean_ctor_set(v___x_1473_, 0, v_msgData_1460_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_msgData_1460_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_msgData_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1478_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Lean_MessageData_ofSyntax(v_after_1471_);
v___x_1481_ = l_Lean_indentD(v___x_1480_);
v_msgData_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1482_, 0, v___x_1479_);
lean_ctor_set(v_msgData_1482_, 1, v___x_1481_);
v___x_1483_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_msgData_1482_, v_macroStack_1461_);
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_1488_, lean_object* v_macroStack_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1488_, v_macroStack_1489_, v___y_1490_);
lean_dec_ref(v___y_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v_env_1500_; lean_object* v___x_1501_; lean_object* v_toCold_1502_; lean_object* v_mctx_1503_; lean_object* v_lctx_1504_; lean_object* v_options_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1499_ = lean_st_ref_get(v___y_1497_);
v_env_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc_ref(v_env_1500_);
lean_dec(v___x_1499_);
v___x_1501_ = lean_st_ref_get(v___y_1495_);
v_toCold_1502_ = lean_ctor_get(v___y_1496_, 0);
v_mctx_1503_ = lean_ctor_get(v___x_1501_, 0);
lean_inc_ref(v_mctx_1503_);
lean_dec(v___x_1501_);
v_lctx_1504_ = lean_ctor_get(v___y_1494_, 2);
v_options_1505_ = lean_ctor_get(v_toCold_1502_, 2);
lean_inc_ref(v_options_1505_);
lean_inc_ref(v_lctx_1504_);
v___x_1506_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1506_, 0, v_env_1500_);
lean_ctor_set(v___x_1506_, 1, v_mctx_1503_);
lean_ctor_set(v___x_1506_, 2, v_lctx_1504_);
lean_ctor_set(v___x_1506_, 3, v_options_1505_);
v___x_1507_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v_msgData_1493_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msgData_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_ref_1524_; lean_object* v___x_1525_; lean_object* v_a_1526_; lean_object* v_macroStack_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1538_; 
v_ref_1524_ = lean_ctor_get(v___y_1521_, 2);
v___x_1525_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_1516_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref(v___x_1525_);
v_macroStack_1527_ = lean_ctor_get(v___y_1517_, 1);
v___x_1528_ = l_Lean_Elab_getBetterRef(v_ref_1524_, v_macroStack_1527_);
lean_inc(v_macroStack_1527_);
v___x_1529_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_1526_, v_macroStack_1527_, v___y_1521_);
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1528_);
lean_ctor_set(v___x_1534_, 1, v_a_1530_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 1);
lean_ctor_set(v___x_1532_, 0, v___x_1534_);
v___x_1536_ = v___x_1532_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1547_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__0));
v___x_1550_ = l_Lean_stringToMessageData(v___x_1549_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__2));
v___x_1553_ = l_Lean_stringToMessageData(v___x_1552_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1557_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__6));
v___x_1558_ = lean_unsigned_to_nat(11u);
v___x_1559_ = lean_unsigned_to_nat(122u);
v___x_1560_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__5));
v___x_1561_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__4));
v___x_1562_ = l_mkPanicMessageWithDecl(v___x_1561_, v___x_1560_, v___x_1559_, v___x_1558_, v___x_1557_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(lean_object* v_constName_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1579_; lean_object* v_env_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; 
v___x_1579_ = lean_st_ref_get(v___y_1569_);
v_env_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc_ref(v_env_1580_);
lean_dec(v___x_1579_);
v___x_1581_ = 0;
lean_inc(v_constName_1563_);
v___x_1582_ = l_Lean_Environment_findAsync_x3f(v_env_1580_, v_constName_1563_, v___x_1581_);
if (lean_obj_tag(v___x_1582_) == 1)
{
lean_object* v_val_1583_; uint8_t v_kind_1584_; 
v_val_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_val_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v_kind_1584_ = lean_ctor_get_uint8(v_val_1583_, sizeof(void*)*3);
if (v_kind_1584_ == 6)
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1583_);
if (lean_obj_tag(v___x_1585_) == 6)
{
lean_object* v_val_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_constName_1563_);
v_val_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_val_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 0);
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_val_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec_ref(v___x_1585_);
v___x_1594_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__7);
v___x_1595_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__1(v___x_1594_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1604_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
if (lean_obj_tag(v_a_1596_) == 0)
{
lean_del_object(v___x_1598_);
goto v___jp_1571_;
}
else
{
lean_object* v_val_1600_; lean_object* v___x_1602_; 
lean_dec(v_constName_1563_);
v_val_1600_ = lean_ctor_get(v_a_1596_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v_a_1596_, 1);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v_val_1600_);
v___x_1602_ = v___x_1598_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_constName_1563_);
v_a_1605_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1595_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1595_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
else
{
lean_dec(v_val_1583_);
goto v___jp_1571_;
}
}
else
{
lean_dec(v___x_1582_);
goto v___jp_1571_;
}
v___jp_1571_:
{
lean_object* v___x_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1572_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_1573_ = 0;
v___x_1574_ = l_Lean_MessageData_ofConstName(v_constName_1563_, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1572_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__3);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v___x_1577_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___boxed(lean_object* v_constName_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v_constName_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(lean_object* v_indVal_1623_, lean_object* v_auxFunName_1624_, lean_object* v_as_x27_1625_, lean_object* v_b_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
if (lean_obj_tag(v_as_x27_1625_) == 0)
{
lean_object* v___x_1634_; 
lean_dec(v_auxFunName_1624_);
lean_dec_ref(v_indVal_1623_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_b_1626_);
return v___x_1634_;
}
else
{
lean_object* v_head_1635_; lean_object* v_tail_1636_; lean_object* v___x_1637_; 
v_head_1635_ = lean_ctor_get(v_as_x27_1625_, 0);
v_tail_1636_ = lean_ctor_get(v_as_x27_1625_, 1);
lean_inc(v_head_1635_);
v___x_1637_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v_head_1635_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v_toConstantVal_1639_; lean_object* v_numFields_1640_; lean_object* v_type_1641_; lean_object* v___f_1642_; lean_object* v___x_1643_; lean_object* v_alts_1644_; lean_object* v___f_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v_toConstantVal_1639_ = lean_ctor_get(v_a_1638_, 0);
lean_inc_ref(v_toConstantVal_1639_);
v_numFields_1640_ = lean_ctor_get(v_a_1638_, 4);
lean_inc(v_numFields_1640_);
lean_dec(v_a_1638_);
v_type_1641_ = lean_ctor_get(v_toConstantVal_1639_, 2);
lean_inc_ref(v_type_1641_);
lean_dec_ref(v_toConstantVal_1639_);
v___f_1642_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0));
v___x_1643_ = lean_unsigned_to_nat(0u);
v_alts_1644_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
lean_inc(v_head_1635_);
lean_inc(v_auxFunName_1624_);
lean_inc_ref(v_indVal_1623_);
v___f_1645_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___boxed), 16, 7);
lean_closure_set(v___f_1645_, 0, v_indVal_1623_);
lean_closure_set(v___f_1645_, 1, v___x_1643_);
lean_closure_set(v___f_1645_, 2, v_alts_1644_);
lean_closure_set(v___f_1645_, 3, v_numFields_1640_);
lean_closure_set(v___f_1645_, 4, v_auxFunName_1624_);
lean_closure_set(v___f_1645_, 5, v___f_1642_);
lean_closure_set(v___f_1645_, 6, v_head_1635_);
v___x_1646_ = 0;
v___x_1647_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_1641_, v___f_1645_, v___x_1646_, v___x_1646_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = lean_array_push(v_b_1626_, v_a_1648_);
v_as_x27_1625_ = v_tail_1636_;
v_b_1626_ = v___x_1649_;
goto _start;
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v_b_1626_);
lean_dec(v_auxFunName_1624_);
lean_dec_ref(v_indVal_1623_);
v_a_1651_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1647_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1647_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v_b_1626_);
lean_dec(v_auxFunName_1624_);
lean_dec_ref(v_indVal_1623_);
v_a_1659_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1637_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1637_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object* v_indVal_1667_, lean_object* v_auxFunName_1668_, lean_object* v_as_x27_1669_, lean_object* v_b_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1667_, v_auxFunName_1668_, v_as_x27_1669_, v_b_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v_as_x27_1669_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(size_t v_sz_1679_, size_t v_i_1680_, lean_object* v_bs_1681_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_usize_dec_lt(v_i_1680_, v_sz_1679_);
if (v___x_1682_ == 0)
{
return v_bs_1681_;
}
else
{
lean_object* v_v_1683_; lean_object* v___x_1684_; lean_object* v_bs_x27_1685_; size_t v___x_1686_; size_t v___x_1687_; lean_object* v___x_1688_; 
v_v_1683_ = lean_array_uget(v_bs_1681_, v_i_1680_);
v___x_1684_ = lean_unsigned_to_nat(0u);
v_bs_x27_1685_ = lean_array_uset(v_bs_1681_, v_i_1680_, v___x_1684_);
v___x_1686_ = ((size_t)1ULL);
v___x_1687_ = lean_usize_add(v_i_1680_, v___x_1686_);
v___x_1688_ = lean_array_uset(v_bs_x27_1685_, v_i_1680_, v_v_1683_);
v_i_1680_ = v___x_1687_;
v_bs_1681_ = v___x_1688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6___boxed(lean_object* v_sz_1690_, lean_object* v_i_1691_, lean_object* v_bs_1692_){
_start:
{
size_t v_sz_boxed_1693_; size_t v_i_boxed_1694_; lean_object* v_res_1695_; 
v_sz_boxed_1693_ = lean_unbox_usize(v_sz_1690_);
lean_dec(v_sz_1690_);
v_i_boxed_1694_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(v_sz_boxed_1693_, v_i_boxed_1694_, v_bs_1692_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(lean_object* v_indVal_1696_, lean_object* v_auxFunName_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_ctors_1705_; lean_object* v_alts_1706_; lean_object* v___x_1707_; 
v_ctors_1705_ = lean_ctor_get(v_indVal_1696_, 4);
v_alts_1706_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
lean_inc_ref(v_indVal_1696_);
v___x_1707_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1696_, v_auxFunName_1697_, v_ctors_1705_, v_alts_1706_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt(v_indVal_1696_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
lean_dec_ref(v_indVal_1696_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1721_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1721_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1721_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; size_t v_sz_1715_; size_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1714_ = lean_array_push(v_a_1708_, v_a_1710_);
v_sz_1715_ = lean_array_size(v___x_1714_);
v___x_1716_ = ((size_t)0ULL);
v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__6(v_sz_1715_, v___x_1716_, v___x_1714_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1717_);
v___x_1719_ = v___x_1712_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_a_1708_);
v_a_1722_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1709_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1709_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_dec_ref(v_indVal_1696_);
return v___x_1707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts___boxed(lean_object* v_indVal_1730_, lean_object* v_auxFunName_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(v_indVal_1730_, v_auxFunName_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1(lean_object* v_upperBound_1740_, lean_object* v_inst_1741_, lean_object* v_R_1742_, lean_object* v_a_1743_, lean_object* v_b_1744_, lean_object* v_c_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg(v_upperBound_1740_, v_a_1743_, v_b_1744_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___boxed(lean_object* v_upperBound_1754_, lean_object* v_inst_1755_, lean_object* v_R_1756_, lean_object* v_a_1757_, lean_object* v_b_1758_, lean_object* v_c_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1(v_upperBound_1754_, v_inst_1755_, v_R_1756_, v_a_1757_, v_b_1758_, v_c_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v_upperBound_1754_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2(lean_object* v___x_1768_, lean_object* v_as_1769_, size_t v_i_1770_, size_t v_stop_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___redArg(v___x_1768_, v_as_1769_, v_i_1770_, v_stop_1771_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2___boxed(lean_object* v___x_1780_, lean_object* v_as_1781_, lean_object* v_i_1782_, lean_object* v_stop_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
size_t v_i_boxed_1791_; size_t v_stop_boxed_1792_; lean_object* v_res_1793_; 
v_i_boxed_1791_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_stop_boxed_1792_ = lean_unbox_usize(v_stop_1783_);
lean_dec(v_stop_1783_);
v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__2(v___x_1780_, v_as_1781_, v_i_boxed_1791_, v_stop_boxed_1792_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v_as_1781_);
lean_dec_ref(v___x_1780_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3(lean_object* v_upperBound_1794_, lean_object* v_indVal_1795_, lean_object* v___x_1796_, lean_object* v_xs_1797_, lean_object* v_a_1798_, lean_object* v_auxFunName_1799_, lean_object* v_inst_1800_, lean_object* v_R_1801_, lean_object* v_a_1802_, lean_object* v_b_1803_, lean_object* v_c_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_1794_, v_indVal_1795_, v___x_1796_, v_xs_1797_, v_a_1798_, v_auxFunName_1799_, v_a_1802_, v_b_1803_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1813_ = _args[0];
lean_object* v_indVal_1814_ = _args[1];
lean_object* v___x_1815_ = _args[2];
lean_object* v_xs_1816_ = _args[3];
lean_object* v_a_1817_ = _args[4];
lean_object* v_auxFunName_1818_ = _args[5];
lean_object* v_inst_1819_ = _args[6];
lean_object* v_R_1820_ = _args[7];
lean_object* v_a_1821_ = _args[8];
lean_object* v_b_1822_ = _args[9];
lean_object* v_c_1823_ = _args[10];
lean_object* v___y_1824_ = _args[11];
lean_object* v___y_1825_ = _args[12];
lean_object* v___y_1826_ = _args[13];
lean_object* v___y_1827_ = _args[14];
lean_object* v___y_1828_ = _args[15];
lean_object* v___y_1829_ = _args[16];
lean_object* v___y_1830_ = _args[17];
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3(v_upperBound_1813_, v_indVal_1814_, v___x_1815_, v_xs_1816_, v_a_1817_, v_auxFunName_1818_, v_inst_1819_, v_R_1820_, v_a_1821_, v_b_1822_, v_c_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec_ref(v_a_1817_);
lean_dec(v___x_1815_);
lean_dec(v_upperBound_1813_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5(lean_object* v_indVal_1832_, lean_object* v_auxFunName_1833_, lean_object* v_as_1834_, lean_object* v_as_x27_1835_, lean_object* v_b_1836_, lean_object* v_a_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg(v_indVal_1832_, v_auxFunName_1833_, v_as_x27_1835_, v_b_1836_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___boxed(lean_object* v_indVal_1846_, lean_object* v_auxFunName_1847_, lean_object* v_as_1848_, lean_object* v_as_x27_1849_, lean_object* v_b_1850_, lean_object* v_a_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5(v_indVal_1846_, v_auxFunName_1847_, v_as_1848_, v_as_x27_1849_, v_b_1850_, v_a_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v_as_x27_1849_);
lean_dec(v_as_1848_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1860_, lean_object* v_msg_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1870_, lean_object* v_msg_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0(v_00_u03b1_1870_, v_msg_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1880_, lean_object* v_macroStack_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1880_, v_macroStack_1881_, v___y_1886_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1890_, lean_object* v_macroStack_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(v_msgData_1890_, v_macroStack_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(lean_object* v_header_1913_, lean_object* v_indVal_1914_, lean_object* v_auxFunName_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v___x_1923_; 
lean_inc_ref(v_indVal_1914_);
v___x_1923_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_1913_, v_indVal_1914_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts(v_indVal_1914_, v_auxFunName_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1956_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1956_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1956_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v_ref_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; size_t v_sz_1939_; size_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v_ref_1930_ = lean_ctor_get(v_a_1920_, 2);
v___x_1931_ = 0;
v___x_1932_ = l_Lean_SourceInfo_fromRef(v_ref_1930_, v___x_1931_);
v___x_1933_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0));
v___x_1934_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1));
lean_inc_n(v___x_1932_, 6);
v___x_1935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1932_);
lean_ctor_set(v___x_1935_, 1, v___x_1933_);
v___x_1936_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_1937_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_1938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1932_);
lean_ctor_set(v___x_1938_, 1, v___x_1936_);
lean_ctor_set(v___x_1938_, 2, v___x_1937_);
v_sz_1939_ = lean_array_size(v_a_1924_);
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__0(v_sz_1939_, v___x_1940_, v_a_1924_);
v___x_1942_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__15);
v___x_1943_ = l_Lean_mkSepArray(v___x_1941_, v___x_1942_);
lean_dec_ref(v___x_1941_);
v___x_1944_ = l_Array_append___redArg(v___x_1937_, v___x_1943_);
lean_dec_ref(v___x_1943_);
v___x_1945_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1932_);
lean_ctor_set(v___x_1945_, 1, v___x_1936_);
lean_ctor_set(v___x_1945_, 2, v___x_1944_);
v___x_1946_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2));
v___x_1947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1932_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4));
v___x_1949_ = l_Array_append___redArg(v___x_1937_, v_a_1926_);
lean_dec(v_a_1926_);
v___x_1950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1932_);
lean_ctor_set(v___x_1950_, 1, v___x_1936_);
lean_ctor_set(v___x_1950_, 2, v___x_1949_);
v___x_1951_ = l_Lean_Syntax_node1(v___x_1932_, v___x_1948_, v___x_1950_);
lean_inc_ref(v___x_1938_);
v___x_1952_ = l_Lean_Syntax_node6(v___x_1932_, v___x_1934_, v___x_1935_, v___x_1938_, v___x_1938_, v___x_1945_, v___x_1947_, v___x_1951_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1952_);
v___x_1954_ = v___x_1928_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v_a_1924_);
v_a_1957_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1925_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1925_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec(v_auxFunName_1915_);
lean_dec_ref(v_indVal_1914_);
v_a_1965_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1923_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1923_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___boxed(lean_object* v_header_1973_, lean_object* v_indVal_1974_, lean_object* v_auxFunName_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(v_header_1973_, v_indVal_1974_, v_auxFunName_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
return v_res_1983_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(lean_object* v_msg_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_37346__overap_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___closed__0);
v___x_37346__overap_1994_ = lean_panic_fn_borrowed(v___x_1993_, v_msg_1985_);
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
v___x_1995_ = lean_apply_7(v___x_37346__overap_1994_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, lean_box(0));
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0___boxed(lean_object* v_msg_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(v_msg_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(lean_object* v___x_2005_, lean_object* v_as_2006_, size_t v_i_2007_, size_t v_stop_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_usize_dec_eq(v_i_2007_, v_stop_2008_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_array_uget_borrowed(v_as_2006_, v_i_2007_);
lean_inc(v___y_2012_);
lean_inc_ref(v___y_2011_);
lean_inc(v___y_2010_);
lean_inc_ref(v___y_2009_);
lean_inc(v___x_2015_);
v___x_2016_ = lean_infer_type(v___x_2015_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2029_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2029_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2029_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
uint8_t v___x_2021_; 
v___x_2021_ = l_Lean_Expr_containsFVar(v_a_2017_, v___x_2005_);
lean_dec(v_a_2017_);
if (v___x_2021_ == 0)
{
size_t v___x_2022_; size_t v___x_2023_; 
lean_del_object(v___x_2019_);
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_2007_, v___x_2022_);
v_i_2007_ = v___x_2023_;
goto _start;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = lean_box(v___x_2021_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2025_);
v___x_2027_ = v___x_2019_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
v_a_2030_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2016_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2016_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
uint8_t v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2038_ = 0;
v___x_2039_ = lean_box(v___x_2038_);
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg___boxed(lean_object* v___x_2041_, lean_object* v_as_2042_, lean_object* v_i_2043_, lean_object* v_stop_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
size_t v_i_boxed_2050_; size_t v_stop_boxed_2051_; lean_object* v_res_2052_; 
v_i_boxed_2050_ = lean_unbox_usize(v_i_2043_);
lean_dec(v_i_2043_);
v_stop_boxed_2051_ = lean_unbox_usize(v_stop_2044_);
lean_dec(v_stop_2044_);
v_res_2052_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_2041_, v_as_2042_, v_i_boxed_2050_, v_stop_boxed_2051_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec_ref(v_as_2042_);
lean_dec(v___x_2041_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(lean_object* v_upperBound_2054_, lean_object* v_indVal_2055_, lean_object* v___x_2056_, lean_object* v_xs_2057_, lean_object* v_a_2058_, lean_object* v___x_2059_, lean_object* v_auxFunName_2060_, lean_object* v_a_2061_, lean_object* v_b_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_nat_dec_lt(v_a_2061_, v_upperBound_2054_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_b_2062_);
return v___x_2071_;
}
else
{
lean_object* v_snd_2072_; lean_object* v_snd_2073_; lean_object* v_fst_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2405_; 
v_snd_2072_ = lean_ctor_get(v_b_2062_, 1);
lean_inc(v_snd_2072_);
v_snd_2073_ = lean_ctor_get(v_snd_2072_, 1);
lean_inc(v_snd_2073_);
v_fst_2074_ = lean_ctor_get(v_b_2062_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_b_2062_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; 
v_unused_2406_ = lean_ctor_get(v_b_2062_, 1);
lean_dec(v_unused_2406_);
v___x_2076_ = v_b_2062_;
v_isShared_2077_ = v_isSharedCheck_2405_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_fst_2074_);
lean_dec(v_b_2062_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2405_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_fst_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2403_; 
v_fst_2078_ = lean_ctor_get(v_snd_2072_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_snd_2072_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v_snd_2072_, 1);
lean_dec(v_unused_2404_);
v___x_2080_ = v_snd_2072_;
v_isShared_2081_ = v_isSharedCheck_2403_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_fst_2078_);
lean_dec(v_snd_2072_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2403_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_fst_2082_; lean_object* v_snd_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2402_; 
v_fst_2082_ = lean_ctor_get(v_snd_2073_, 0);
v_snd_2083_ = lean_ctor_get(v_snd_2073_, 1);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_snd_2073_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2085_ = v_snd_2073_;
v_isShared_2086_ = v_isSharedCheck_2402_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_snd_2083_);
lean_inc(v_fst_2082_);
lean_dec(v_snd_2073_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2402_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_numParams_2087_; lean_object* v___x_2088_; lean_object* v_a_2090_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_numParams_2087_ = lean_ctor_get(v_indVal_2055_, 1);
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2093_ = l_Lean_instInhabitedExpr;
v___x_2094_ = lean_nat_add(v_numParams_2087_, v___x_2056_);
v___x_2095_ = lean_nat_sub(v___x_2094_, v_a_2061_);
lean_dec(v___x_2094_);
v___x_2096_ = lean_nat_sub(v___x_2095_, v___x_2088_);
lean_dec(v___x_2095_);
v___x_2097_ = lean_array_get_borrowed(v___x_2093_, v_xs_2057_, v___x_2096_);
v___x_2098_ = l_Lean_Expr_fvarId_x21(v___x_2097_);
v___x_2099_ = l_Lean_Expr_containsFVar(v_a_2058_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; 
lean_inc(v___x_2098_);
v___x_2100_ = l_Lean_FVarId_getUserName___redArg(v___x_2098_, v___y_2065_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc_n(v_a_2101_, 2);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = l_Lean_Core_mkFreshUserName(v_a_2101_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2104_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___closed__0));
v___x_2105_ = lean_name_append_after(v_a_2101_, v___x_2104_);
v___x_2106_ = l_Lean_Core_mkFreshUserName(v___x_2105_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
lean_inc(v___y_2068_);
lean_inc_ref(v___y_2067_);
lean_inc(v___y_2066_);
lean_inc_ref(v___y_2065_);
lean_inc(v___x_2097_);
v___x_2108_ = lean_infer_type(v___x_2097_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2110_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc_n(v_a_2109_, 2);
lean_dec_ref_known(v___x_2108_, 1);
v___x_2110_ = l_Lean_Meta_isProp(v_a_2109_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v_a_2117_; uint8_t v___x_2170_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = l_Lean_mkIdent(v_a_2103_);
v___x_2113_ = l_Lean_mkIdent(v_a_2107_);
lean_inc(v___x_2112_);
v___x_2114_ = lean_array_push(v_fst_2074_, v___x_2112_);
lean_inc(v___x_2113_);
v___x_2115_ = lean_array_push(v_fst_2078_, v___x_2113_);
v___x_2170_ = lean_unbox(v_a_2111_);
if (v___x_2170_ == 0)
{
uint8_t v___x_2171_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v_lower_2281_; lean_object* v_upper_2282_; 
v___x_2171_ = l_Lean_Expr_isAppOf(v_a_2109_, v___x_2059_);
lean_dec(v_a_2109_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; 
lean_dec(v_a_2111_);
v___x_2290_ = lean_nat_add(v___x_2096_, v___x_2088_);
lean_dec(v___x_2096_);
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = lean_array_get_size(v_xs_2057_);
v___x_2293_ = lean_nat_dec_le(v___x_2290_, v___x_2291_);
if (v___x_2293_ == 0)
{
v_lower_2281_ = v___x_2290_;
v_upper_2282_ = v___x_2292_;
goto v___jp_2280_;
}
else
{
lean_dec(v___x_2290_);
v_lower_2281_ = v___x_2291_;
v_upper_2282_ = v___x_2292_;
goto v___jp_2280_;
}
}
else
{
uint8_t v___x_2294_; 
lean_dec(v___x_2098_);
lean_dec(v___x_2096_);
lean_del_object(v___x_2085_);
lean_del_object(v___x_2080_);
lean_del_object(v___x_2076_);
v___x_2294_ = lean_unbox(v_snd_2083_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; 
lean_dec(v_a_2111_);
v___x_2295_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc_n(v_a_2296_, 4);
lean_dec_ref_known(v___x_2295_, 1);
v___x_2297_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_2298_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_2060_);
v___x_2299_ = l_Lean_mkIdent(v_auxFunName_2060_);
v___x_2300_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2301_ = l_Lean_Syntax_node2(v_a_2296_, v___x_2300_, v___x_2112_, v___x_2113_);
v___x_2302_ = l_Lean_Syntax_node2(v_a_2296_, v___x_2298_, v___x_2299_, v___x_2301_);
v___x_2303_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_2304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2304_, 0, v_a_2296_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = l_Lean_Syntax_node3(v_a_2296_, v___x_2297_, v___x_2302_, v___x_2304_, v_fst_2082_);
v___x_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v_snd_2083_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2115_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2114_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v_a_2090_ = v___x_2308_;
goto v___jp_2089_;
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v___x_2114_);
lean_dec(v___x_2113_);
lean_dec(v___x_2112_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2309_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2295_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2295_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
else
{
lean_object* v___x_2317_; 
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
v___x_2317_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc_n(v_a_2318_, 2);
lean_dec_ref_known(v___x_2317_, 1);
v___x_2319_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
lean_inc(v_auxFunName_2060_);
v___x_2320_ = l_Lean_mkIdent(v_auxFunName_2060_);
v___x_2321_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2322_ = l_Lean_Syntax_node2(v_a_2318_, v___x_2321_, v___x_2112_, v___x_2113_);
v___x_2323_ = l_Lean_Syntax_node2(v_a_2318_, v___x_2319_, v___x_2320_, v___x_2322_);
v___x_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
lean_ctor_set(v___x_2324_, 1, v_a_2111_);
v___x_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2115_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2114_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v_a_2090_ = v___x_2326_;
goto v___jp_2089_;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v___x_2114_);
lean_dec(v___x_2113_);
lean_dec(v___x_2112_);
lean_dec(v_a_2111_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2327_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2317_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2317_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
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
v___jp_2172_:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_nat_dec_lt(v___y_2173_, v___y_2175_);
if (v___x_2176_ == 0)
{
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec(v___x_2098_);
v_a_2117_ = v___x_2176_;
goto v___jp_2116_;
}
else
{
size_t v___x_2177_; size_t v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_usize_of_nat(v___y_2173_);
lean_dec(v___y_2173_);
v___x_2178_ = lean_usize_of_nat(v___y_2175_);
lean_dec(v___y_2175_);
v___x_2179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_2098_, v___y_2174_, v___x_2177_, v___x_2178_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec_ref(v___y_2174_);
lean_dec(v___x_2098_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; uint8_t v___x_2181_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2181_ = lean_unbox(v_a_2180_);
if (v___x_2181_ == 0)
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_unbox(v_a_2180_);
lean_dec(v_a_2180_);
v_a_2117_ = v___x_2182_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2183_; 
lean_dec(v_a_2180_);
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_del_object(v___x_2080_);
lean_del_object(v___x_2076_);
v___x_2183_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_toCold_2184_; lean_object* v_a_2185_; lean_object* v_quotContext_2186_; lean_object* v_currMacroScope_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v_toCold_2184_ = lean_ctor_get(v___y_2067_, 0);
v_a_2185_ = lean_ctor_get(v___x_2183_, 0);
lean_inc_n(v_a_2185_, 31);
lean_dec_ref_known(v___x_2183_, 1);
v_quotContext_2186_ = lean_ctor_get(v_toCold_2184_, 8);
v_currMacroScope_2187_ = lean_ctor_get(v_toCold_2184_, 9);
v___x_2188_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__11));
v___x_2189_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__12));
v___x_2190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_a_2185_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__14));
v___x_2192_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_2193_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
lean_inc_n(v_currMacroScope_2187_, 4);
lean_inc_n(v_quotContext_2186_, 4);
v___x_2194_ = l_Lean_addMacroScope(v_quotContext_2186_, v___x_2193_, v_currMacroScope_2187_);
v___x_2195_ = lean_box(0);
v___x_2196_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2196_, 0, v_a_2185_);
lean_ctor_set(v___x_2196_, 1, v___x_2192_);
lean_ctor_set(v___x_2196_, 2, v___x_2194_);
lean_ctor_set(v___x_2196_, 3, v___x_2195_);
lean_inc_ref(v___x_2196_);
v___x_2197_ = l_Lean_Syntax_node1(v_a_2185_, v___x_2191_, v___x_2196_);
v___x_2198_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_2199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2199_, 0, v_a_2185_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2201_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2202_, 0, v_a_2185_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = l_Lean_Syntax_node3(v_a_2185_, v___x_2200_, v___x_2112_, v___x_2202_, v___x_2113_);
v___x_2204_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__19));
v___x_2205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_a_2185_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__21));
v___x_2207_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__22));
v___x_2208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_a_2185_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__25));
v___x_2210_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__27));
v___x_2211_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2212_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__28));
v___x_2213_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__29));
v___x_2214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2214_, 0, v_a_2185_);
lean_ctor_set(v___x_2214_, 1, v___x_2212_);
v___x_2215_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__31));
v___x_2216_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2217_, 0, v_a_2185_);
lean_ctor_set(v___x_2217_, 1, v___x_2211_);
lean_ctor_set(v___x_2217_, 2, v___x_2216_);
v___x_2218_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_2219_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2220_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_2221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2221_, 0, v_a_2185_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2223_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_2224_ = lean_box(0);
v___x_2225_ = l_Lean_addMacroScope(v_quotContext_2186_, v___x_2224_, v_currMacroScope_2187_);
v___x_2226_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__50));
v___x_2227_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2227_, 0, v_a_2185_);
lean_ctor_set(v___x_2227_, 1, v___x_2223_);
lean_ctor_set(v___x_2227_, 2, v___x_2225_);
lean_ctor_set(v___x_2227_, 3, v___x_2226_);
v___x_2228_ = l_Lean_Syntax_node1(v_a_2185_, v___x_2222_, v___x_2227_);
v___x_2229_ = l_Lean_Syntax_node2(v_a_2185_, v___x_2219_, v___x_2221_, v___x_2228_);
v___x_2230_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2231_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__54);
v___x_2232_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__55));
v___x_2233_ = l_Lean_addMacroScope(v_quotContext_2186_, v___x_2232_, v_currMacroScope_2187_);
v___x_2234_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__59));
v___x_2235_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2235_, 0, v_a_2185_);
lean_ctor_set(v___x_2235_, 1, v___x_2231_);
lean_ctor_set(v___x_2235_, 2, v___x_2233_);
lean_ctor_set(v___x_2235_, 3, v___x_2234_);
v___x_2236_ = l_Lean_Syntax_node1(v_a_2185_, v___x_2211_, v___x_2196_);
v___x_2237_ = l_Lean_Syntax_node2(v_a_2185_, v___x_2230_, v___x_2235_, v___x_2236_);
v___x_2238_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_a_2185_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = l_Lean_Syntax_node3(v_a_2185_, v___x_2218_, v___x_2229_, v___x_2237_, v___x_2239_);
lean_inc_ref_n(v___x_2217_, 3);
v___x_2241_ = l_Lean_Syntax_node2(v_a_2185_, v___x_2215_, v___x_2217_, v___x_2240_);
v___x_2242_ = l_Lean_Syntax_node1(v_a_2185_, v___x_2211_, v___x_2241_);
v___x_2243_ = l_Lean_Syntax_node4(v_a_2185_, v___x_2213_, v___x_2214_, v___x_2242_, v___x_2217_, v___x_2217_);
v___x_2244_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__61));
v___x_2245_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__62));
v___x_2246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2246_, 0, v_a_2185_);
lean_ctor_set(v___x_2246_, 1, v___x_2244_);
v___x_2247_ = l_Lean_Syntax_node2(v_a_2185_, v___x_2245_, v___x_2246_, v_fst_2082_);
v___x_2248_ = l_Lean_Syntax_node3(v_a_2185_, v___x_2211_, v___x_2243_, v___x_2217_, v___x_2247_);
v___x_2249_ = l_Lean_Syntax_node1(v_a_2185_, v___x_2210_, v___x_2248_);
v___x_2250_ = l_Lean_Syntax_node1(v_a_2185_, v___x_2209_, v___x_2249_);
v___x_2251_ = l_Lean_Syntax_node2(v_a_2185_, v___x_2206_, v___x_2208_, v___x_2250_);
v___x_2252_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__63));
v___x_2253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2253_, 0, v_a_2185_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_2255_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_2256_ = l_Lean_addMacroScope(v_quotContext_2186_, v___x_2255_, v_currMacroScope_2187_);
v___x_2257_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__65));
v___x_2258_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2258_, 0, v_a_2185_);
lean_ctor_set(v___x_2258_, 1, v___x_2254_);
lean_ctor_set(v___x_2258_, 2, v___x_2256_);
lean_ctor_set(v___x_2258_, 3, v___x_2257_);
v___x_2259_ = l_Lean_Syntax_node8(v_a_2185_, v___x_2188_, v___x_2190_, v___x_2197_, v___x_2199_, v___x_2203_, v___x_2205_, v___x_2251_, v___x_2253_, v___x_2258_);
v___x_2260_ = lean_box(v___x_2171_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2115_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2114_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v_a_2090_ = v___x_2263_;
goto v___jp_2089_;
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v___x_2114_);
lean_dec(v___x_2113_);
lean_dec(v___x_2112_);
lean_dec(v_fst_2082_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2264_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2183_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2183_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v___x_2114_);
lean_dec(v___x_2113_);
lean_dec(v___x_2112_);
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_del_object(v___x_2080_);
lean_del_object(v___x_2076_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2272_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2179_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2179_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
v___jp_2280_:
{
lean_object* v___x_2283_; lean_object* v_array_2284_; lean_object* v_start_2285_; lean_object* v_stop_2286_; uint8_t v___x_2287_; 
lean_inc_ref(v_xs_2057_);
v___x_2283_ = l_Array_toSubarray___redArg(v_xs_2057_, v_lower_2281_, v_upper_2282_);
v_array_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc_ref(v_array_2284_);
v_start_2285_ = lean_ctor_get(v___x_2283_, 1);
lean_inc(v_start_2285_);
v_stop_2286_ = lean_ctor_get(v___x_2283_, 2);
lean_inc(v_stop_2286_);
lean_dec_ref(v___x_2283_);
v___x_2287_ = lean_nat_dec_lt(v_start_2285_, v_stop_2286_);
if (v___x_2287_ == 0)
{
lean_dec(v_stop_2286_);
lean_dec(v_start_2285_);
lean_dec_ref(v_array_2284_);
lean_dec(v___x_2098_);
v_a_2117_ = v___x_2287_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2288_ = lean_array_get_size(v_array_2284_);
v___x_2289_ = lean_nat_dec_le(v_stop_2286_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_dec(v_stop_2286_);
v___y_2173_ = v_start_2285_;
v___y_2174_ = v_array_2284_;
v___y_2175_ = v___x_2288_;
goto v___jp_2172_;
}
else
{
v___y_2173_ = v_start_2285_;
v___y_2174_ = v_array_2284_;
v___y_2175_ = v_stop_2286_;
goto v___jp_2172_;
}
}
}
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec(v___x_2113_);
lean_dec(v___x_2112_);
lean_dec(v_a_2111_);
lean_dec(v_a_2109_);
lean_dec(v___x_2098_);
lean_dec(v___x_2096_);
lean_del_object(v___x_2085_);
lean_del_object(v___x_2080_);
lean_del_object(v___x_2076_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v_fst_2082_);
lean_ctor_set(v___x_2335_, 1, v_snd_2083_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2115_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2114_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v_a_2090_ = v___x_2337_;
goto v___jp_2089_;
}
v___jp_2116_:
{
uint8_t v___x_2118_; 
v___x_2118_ = lean_unbox(v_snd_2083_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
v___x_2119_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc_n(v_a_2120_, 4);
lean_dec_ref_known(v___x_2119_, 1);
v___x_2121_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__5));
v___x_2122_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2123_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2124_, 0, v_a_2120_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = l_Lean_Syntax_node3(v_a_2120_, v___x_2122_, v___x_2112_, v___x_2124_, v___x_2113_);
v___x_2126_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__9));
v___x_2127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2127_, 0, v_a_2120_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = l_Lean_Syntax_node3(v_a_2120_, v___x_2121_, v___x_2125_, v___x_2127_, v_fst_2082_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2128_);
v___x_2130_ = v___x_2085_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_snd_2083_);
v___x_2130_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2132_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 1, v___x_2130_);
lean_ctor_set(v___x_2080_, 0, v___x_2115_);
v___x_2132_ = v___x_2080_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v___x_2132_);
lean_ctor_set(v___x_2076_, 0, v___x_2114_);
v___x_2134_ = v___x_2076_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
v_a_2090_ = v___x_2134_;
goto v___jp_2089_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v___x_2114_);
lean_dec(v___x_2113_);
lean_dec(v___x_2112_);
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_del_object(v___x_2080_);
lean_del_object(v___x_2076_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2138_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2119_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2119_);
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
else
{
lean_object* v___x_2146_; 
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
v___x_2146_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc_n(v_a_2147_, 2);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_2149_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_2150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2150_, 0, v_a_2147_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = l_Lean_Syntax_node3(v_a_2147_, v___x_2148_, v___x_2112_, v___x_2150_, v___x_2113_);
v___x_2152_ = lean_box(v_a_2117_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 1, v___x_2152_);
lean_ctor_set(v___x_2085_, 0, v___x_2151_);
v___x_2154_ = v___x_2085_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2156_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 1, v___x_2154_);
lean_ctor_set(v___x_2080_, 0, v___x_2115_);
v___x_2156_ = v___x_2080_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2158_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v___x_2156_);
lean_ctor_set(v___x_2076_, 0, v___x_2114_);
v___x_2158_ = v___x_2076_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
v_a_2090_ = v___x_2158_;
goto v___jp_2089_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v___x_2114_);
lean_dec(v___x_2113_);
lean_dec(v___x_2112_);
lean_del_object(v___x_2085_);
lean_del_object(v___x_2080_);
lean_del_object(v___x_2076_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2162_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2146_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2146_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_a_2109_);
lean_dec(v_a_2107_);
lean_dec(v_a_2103_);
lean_dec(v___x_2098_);
lean_dec(v___x_2096_);
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_del_object(v___x_2080_);
lean_dec(v_fst_2078_);
lean_del_object(v___x_2076_);
lean_dec(v_fst_2074_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2338_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2110_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2110_);
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
lean_dec(v_a_2107_);
lean_dec(v_a_2103_);
lean_dec(v___x_2098_);
lean_dec(v___x_2096_);
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_del_object(v___x_2080_);
lean_dec(v_fst_2078_);
lean_del_object(v___x_2076_);
lean_dec(v_fst_2074_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2346_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2108_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2108_);
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
lean_dec(v_a_2103_);
lean_dec(v___x_2098_);
lean_dec(v___x_2096_);
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_del_object(v___x_2080_);
lean_dec(v_fst_2078_);
lean_del_object(v___x_2076_);
lean_dec(v_fst_2074_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2354_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2106_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2106_);
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
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v_a_2101_);
lean_dec(v___x_2098_);
lean_dec(v___x_2096_);
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_del_object(v___x_2080_);
lean_dec(v_fst_2078_);
lean_del_object(v___x_2076_);
lean_dec(v_fst_2074_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2362_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2102_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2102_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec(v___x_2098_);
lean_dec(v___x_2096_);
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_del_object(v___x_2080_);
lean_dec(v_fst_2078_);
lean_del_object(v___x_2076_);
lean_dec(v_fst_2074_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2370_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2100_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2100_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
else
{
lean_object* v___x_2378_; 
lean_dec(v___x_2098_);
lean_dec(v___x_2096_);
v___x_2378_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__1___redArg___lam__0(v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc_n(v_a_2379_, 2);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2380_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_2381_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
v___x_2382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_a_2379_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = l_Lean_Syntax_node1(v_a_2379_, v___x_2380_, v___x_2382_);
v___x_2384_ = lean_array_push(v_fst_2074_, v___x_2383_);
if (v_isShared_2086_ == 0)
{
v___x_2386_ = v___x_2085_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_fst_2082_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_snd_2083_);
v___x_2386_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2388_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 1, v___x_2386_);
v___x_2388_ = v___x_2080_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_fst_2078_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v___x_2388_);
lean_ctor_set(v___x_2076_, 0, v___x_2384_);
v___x_2390_ = v___x_2076_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2384_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
v_a_2090_ = v___x_2390_;
goto v___jp_2089_;
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_del_object(v___x_2080_);
lean_dec(v_fst_2078_);
lean_del_object(v___x_2076_);
lean_dec(v_fst_2074_);
lean_dec(v_a_2061_);
lean_dec(v_auxFunName_2060_);
lean_dec_ref(v_xs_2057_);
v_a_2394_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2378_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2378_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
v___jp_2089_:
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_nat_add(v_a_2061_, v___x_2088_);
lean_dec(v_a_2061_);
v_a_2061_ = v___x_2091_;
v_b_2062_ = v_a_2090_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg___boxed(lean_object* v_upperBound_2407_, lean_object* v_indVal_2408_, lean_object* v___x_2409_, lean_object* v_xs_2410_, lean_object* v_a_2411_, lean_object* v___x_2412_, lean_object* v_auxFunName_2413_, lean_object* v_a_2414_, lean_object* v_b_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_upperBound_2407_, v_indVal_2408_, v___x_2409_, v_xs_2410_, v_a_2411_, v___x_2412_, v_auxFunName_2413_, v_a_2414_, v_b_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___x_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v___x_2409_);
lean_dec_ref(v_indVal_2408_);
lean_dec(v_upperBound_2407_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1(uint8_t v_rhs__empty_2451_, lean_object* v_numFields_2452_, lean_object* v_indVal_2453_, lean_object* v_name_2454_, lean_object* v_auxFunName_2455_, lean_object* v___f_2456_, lean_object* v_xs_2457_, lean_object* v_type_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_Core_betaReduce(v_type_2458_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_toCold_2467_; lean_object* v_a_2468_; lean_object* v_ref_2469_; lean_object* v_quotContext_2470_; lean_object* v_currMacroScope_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_toCold_2467_ = lean_ctor_get(v___y_2463_, 0);
v_a_2468_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2466_, 1);
v_ref_2469_ = lean_ctor_get(v___y_2463_, 2);
v_quotContext_2470_ = lean_ctor_get(v_toCold_2467_, 8);
v_currMacroScope_2471_ = lean_ctor_get(v_toCold_2467_, 9);
v___x_2472_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__1);
v___x_2473_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__2));
v___x_2474_ = lean_unsigned_to_nat(0u);
v___x_2475_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
v___x_2476_ = 0;
v___x_2477_ = l_Lean_SourceInfo_fromRef(v_ref_2469_, v___x_2476_);
lean_inc(v_currMacroScope_2471_);
lean_inc(v_quotContext_2470_);
v___x_2478_ = l_Lean_addMacroScope(v_quotContext_2470_, v___x_2473_, v_currMacroScope_2471_);
v___x_2479_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__5));
v___x_2480_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2477_);
lean_ctor_set(v___x_2480_, 1, v___x_2472_);
lean_ctor_set(v___x_2480_, 2, v___x_2478_);
lean_ctor_set(v___x_2480_, 3, v___x_2479_);
v___x_2481_ = lean_box(v_rhs__empty_2451_);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2475_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2475_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_numFields_2452_, v_indVal_2453_, v_numFields_2452_, v_xs_2457_, v_a_2468_, v_name_2454_, v_auxFunName_2455_, v___x_2474_, v___x_2484_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v_a_2468_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v_snd_2487_; lean_object* v_snd_2488_; lean_object* v_fst_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2587_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2485_, 1);
v_snd_2487_ = lean_ctor_get(v_a_2486_, 1);
lean_inc(v_snd_2487_);
v_snd_2488_ = lean_ctor_get(v_snd_2487_, 1);
lean_inc(v_snd_2488_);
v_fst_2489_ = lean_ctor_get(v_a_2486_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_a_2486_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v_a_2486_, 1);
lean_dec(v_unused_2588_);
v___x_2491_ = v_a_2486_;
v_isShared_2492_ = v_isSharedCheck_2587_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_fst_2489_);
lean_dec(v_a_2486_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2587_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_fst_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2585_; 
v_fst_2493_ = lean_ctor_get(v_snd_2487_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_snd_2487_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v_snd_2487_, 1);
lean_dec(v_unused_2586_);
v___x_2495_ = v_snd_2487_;
v_isShared_2496_ = v_isSharedCheck_2585_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_fst_2493_);
lean_dec(v_snd_2487_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2585_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_fst_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2583_; 
v_fst_2497_ = lean_ctor_get(v_snd_2488_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_snd_2488_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; 
v_unused_2584_ = lean_ctor_get(v_snd_2488_, 1);
lean_dec(v_unused_2584_);
v___x_2499_ = v_snd_2488_;
v_isShared_2500_ = v_isSharedCheck_2583_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_fst_2497_);
lean_dec(v_snd_2488_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2583_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v_ctorArgs1_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2552_ = lean_array_get_size(v_fst_2489_);
v___x_2553_ = lean_nat_dec_eq(v___x_2552_, v___x_2474_);
if (v___x_2553_ == 0)
{
v_ctorArgs1_2502_ = v_fst_2489_;
v___y_2503_ = v___y_2459_;
v___y_2504_ = v___y_2460_;
v___y_2505_ = v___y_2461_;
v___y_2506_ = v___y_2462_;
v___y_2507_ = v___y_2463_;
v___y_2508_ = v___y_2464_;
goto v___jp_2501_;
}
else
{
lean_object* v___x_2554_; 
lean_inc_ref(v___f_2456_);
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
lean_inc(v___y_2462_);
lean_inc_ref(v___y_2461_);
lean_inc(v___y_2460_);
lean_inc_ref(v___y_2459_);
v___x_2554_ = lean_apply_7(v___f_2456_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, lean_box(0));
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc_n(v_a_2555_, 7);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__5));
v___x_2557_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2558_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_2559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2559_, 0, v_a_2555_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2561_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
v___x_2562_ = lean_box(0);
lean_inc(v_currMacroScope_2471_);
lean_inc(v_quotContext_2470_);
v___x_2563_ = l_Lean_addMacroScope(v_quotContext_2470_, v___x_2562_, v_currMacroScope_2471_);
v___x_2564_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8));
v___x_2565_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2565_, 0, v_a_2555_);
lean_ctor_set(v___x_2565_, 1, v___x_2561_);
lean_ctor_set(v___x_2565_, 2, v___x_2563_);
lean_ctor_set(v___x_2565_, 3, v___x_2564_);
v___x_2566_ = l_Lean_Syntax_node1(v_a_2555_, v___x_2560_, v___x_2565_);
v___x_2567_ = l_Lean_Syntax_node2(v_a_2555_, v___x_2557_, v___x_2559_, v___x_2566_);
v___x_2568_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2569_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2570_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2570_, 0, v_a_2555_);
lean_ctor_set(v___x_2570_, 1, v___x_2568_);
lean_ctor_set(v___x_2570_, 2, v___x_2569_);
v___x_2571_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2572_, 0, v_a_2555_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = l_Lean_Syntax_node3(v_a_2555_, v___x_2556_, v___x_2567_, v___x_2570_, v___x_2572_);
v___x_2574_ = lean_array_push(v_fst_2489_, v___x_2573_);
v_ctorArgs1_2502_ = v___x_2574_;
v___y_2503_ = v___y_2459_;
v___y_2504_ = v___y_2460_;
v___y_2505_ = v___y_2461_;
v___y_2506_ = v___y_2462_;
v___y_2507_ = v___y_2463_;
v___y_2508_ = v___y_2464_;
goto v___jp_2501_;
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_del_object(v___x_2499_);
lean_dec(v_fst_2497_);
lean_del_object(v___x_2495_);
lean_dec(v_fst_2493_);
lean_del_object(v___x_2491_);
lean_dec(v_fst_2489_);
lean_dec_ref(v___f_2456_);
v_a_2575_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2554_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2554_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
v___jp_2501_:
{
lean_object* v___x_2509_; 
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
v___x_2509_ = lean_apply_7(v___f_2456_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, lean_box(0));
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2543_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2543_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2543_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2514_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__8));
v___x_2515_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__6));
lean_inc(v_a_2510_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set_tag(v___x_2499_, 2);
lean_ctor_set(v___x_2499_, 1, v___x_2515_);
lean_ctor_set(v___x_2499_, 0, v_a_2510_);
v___x_2517_ = v___x_2499_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2510_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__0));
v___x_2519_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__1));
lean_inc(v_a_2510_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 2);
lean_ctor_set(v___x_2495_, 1, v___x_2518_);
lean_ctor_set(v___x_2495_, 0, v_a_2510_);
v___x_2521_ = v___x_2495_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2510_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2518_);
v___x_2521_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2522_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__3));
v___x_2523_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2524_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_2525_ = l_Array_reverse___redArg(v_ctorArgs1_2502_);
v___x_2526_ = l_Array_append___redArg(v___x_2524_, v___x_2525_);
lean_dec_ref(v___x_2525_);
v___x_2527_ = l_Array_reverse___redArg(v_fst_2493_);
v___x_2528_ = l_Array_append___redArg(v___x_2526_, v___x_2527_);
lean_dec_ref(v___x_2527_);
lean_inc_n(v_a_2510_, 3);
v___x_2529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2529_, 0, v_a_2510_);
lean_ctor_set(v___x_2529_, 1, v___x_2523_);
lean_ctor_set(v___x_2529_, 2, v___x_2528_);
v___x_2530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2530_, 0, v_a_2510_);
lean_ctor_set(v___x_2530_, 1, v___x_2523_);
lean_ctor_set(v___x_2530_, 2, v___x_2524_);
v___x_2531_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
if (v_isShared_2492_ == 0)
{
lean_ctor_set_tag(v___x_2491_, 2);
lean_ctor_set(v___x_2491_, 1, v___x_2531_);
lean_ctor_set(v___x_2491_, 0, v_a_2510_);
v___x_2533_ = v___x_2491_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2510_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_inc_n(v_a_2510_, 2);
v___x_2534_ = l_Lean_Syntax_node4(v_a_2510_, v___x_2522_, v___x_2529_, v___x_2530_, v___x_2533_, v_fst_2497_);
v___x_2535_ = l_Lean_Syntax_node2(v_a_2510_, v___x_2519_, v___x_2521_, v___x_2534_);
v___x_2536_ = l_Lean_Syntax_node2(v_a_2510_, v___x_2514_, v___x_2517_, v___x_2535_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2536_);
v___x_2538_ = v___x_2512_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v_ctorArgs1_2502_);
lean_del_object(v___x_2499_);
lean_dec(v_fst_2497_);
lean_del_object(v___x_2495_);
lean_dec(v_fst_2493_);
lean_del_object(v___x_2491_);
v_a_2544_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2509_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2509_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
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
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v___f_2456_);
v_a_2589_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2485_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2485_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec_ref(v_xs_2457_);
lean_dec_ref(v___f_2456_);
lean_dec(v_auxFunName_2455_);
v_a_2597_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2466_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2466_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___boxed(lean_object* v_rhs__empty_2605_, lean_object* v_numFields_2606_, lean_object* v_indVal_2607_, lean_object* v_name_2608_, lean_object* v_auxFunName_2609_, lean_object* v___f_2610_, lean_object* v_xs_2611_, lean_object* v_type_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
uint8_t v_rhs__empty_boxed_2620_; lean_object* v_res_2621_; 
v_rhs__empty_boxed_2620_ = lean_unbox(v_rhs__empty_2605_);
v_res_2621_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1(v_rhs__empty_boxed_2620_, v_numFields_2606_, v_indVal_2607_, v_name_2608_, v_auxFunName_2609_, v___f_2610_, v_xs_2611_, v_type_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v_name_2608_);
lean_dec_ref(v_indVal_2607_);
lean_dec(v_numFields_2606_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0(lean_object* v___x_2622_, lean_object* v_ctors_2623_, uint8_t v_rhs__empty_2624_, lean_object* v_indVal_2625_, lean_object* v_name_2626_, lean_object* v_auxFunName_2627_, lean_object* v___f_2628_, lean_object* v_x_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = l_List_get_x21Internal___redArg(v___x_2622_, v_ctors_2623_, v_x_2629_);
v___x_2638_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0(v___x_2637_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v_toConstantVal_2640_; lean_object* v_numFields_2641_; lean_object* v_type_2642_; lean_object* v___x_2643_; lean_object* v___f_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v_toConstantVal_2640_ = lean_ctor_get(v_a_2639_, 0);
lean_inc_ref(v_toConstantVal_2640_);
v_numFields_2641_ = lean_ctor_get(v_a_2639_, 4);
lean_inc(v_numFields_2641_);
lean_dec(v_a_2639_);
v_type_2642_ = lean_ctor_get(v_toConstantVal_2640_, 2);
lean_inc_ref(v_type_2642_);
lean_dec_ref(v_toConstantVal_2640_);
v___x_2643_ = lean_box(v_rhs__empty_2624_);
v___f_2644_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___boxed), 15, 6);
lean_closure_set(v___f_2644_, 0, v___x_2643_);
lean_closure_set(v___f_2644_, 1, v_numFields_2641_);
lean_closure_set(v___f_2644_, 2, v_indVal_2625_);
lean_closure_set(v___f_2644_, 3, v_name_2626_);
lean_closure_set(v___f_2644_, 4, v_auxFunName_2627_);
lean_closure_set(v___f_2644_, 5, v___f_2628_);
v___x_2645_ = 0;
v___x_2646_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__4___redArg(v_type_2642_, v___f_2644_, v___x_2645_, v___x_2645_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2646_;
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec_ref(v___f_2628_);
lean_dec(v_auxFunName_2627_);
lean_dec(v_name_2626_);
lean_dec_ref(v_indVal_2625_);
v_a_2647_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2638_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2638_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0___boxed(lean_object* v___x_2655_, lean_object* v_ctors_2656_, lean_object* v_rhs__empty_2657_, lean_object* v_indVal_2658_, lean_object* v_name_2659_, lean_object* v_auxFunName_2660_, lean_object* v___f_2661_, lean_object* v_x_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
uint8_t v_rhs__empty_boxed_2670_; lean_object* v_res_2671_; 
v_rhs__empty_boxed_2670_ = lean_unbox(v_rhs__empty_2657_);
v_res_2671_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0(v___x_2655_, v_ctors_2656_, v_rhs__empty_boxed_2670_, v_indVal_2658_, v_name_2659_, v_auxFunName_2660_, v___f_2661_, v_x_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v_ctors_2656_);
lean_dec(v___x_2655_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(lean_object* v_f_2672_, lean_object* v_n_2673_, lean_object* v_x_2674_, lean_object* v_i_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
uint8_t v___x_2683_; 
v___x_2683_ = lean_nat_dec_lt(v_i_2675_, v_n_2673_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; 
lean_dec(v_i_2675_);
lean_dec_ref(v_f_2672_);
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v_x_2674_);
return v___x_2684_;
}
else
{
lean_object* v___x_2685_; 
lean_inc_ref(v_f_2672_);
lean_inc(v___y_2681_);
lean_inc_ref(v___y_2680_);
lean_inc(v___y_2679_);
lean_inc_ref(v___y_2678_);
lean_inc(v___y_2677_);
lean_inc_ref(v___y_2676_);
lean_inc(v_i_2675_);
v___x_2685_ = lean_apply_8(v_f_2672_, v_i_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, lean_box(0));
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2687_ = lean_array_push(v_x_2674_, v_a_2686_);
v___x_2688_ = lean_unsigned_to_nat(1u);
v___x_2689_ = lean_nat_add(v_i_2675_, v___x_2688_);
lean_dec(v_i_2675_);
v_x_2674_ = v___x_2687_;
v_i_2675_ = v___x_2689_;
goto _start;
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_i_2675_);
lean_dec_ref(v_x_2674_);
lean_dec_ref(v_f_2672_);
v_a_2691_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2685_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2685_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg___boxed(lean_object* v_f_2699_, lean_object* v_n_2700_, lean_object* v_x_2701_, lean_object* v_i_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_2699_, v_n_2700_, v_x_2701_, v_i_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v_n_2700_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(lean_object* v_n_2711_, lean_object* v_f_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2720_ = lean_mk_empty_array_with_capacity(v_n_2711_);
v___x_2721_ = lean_unsigned_to_nat(0u);
v___x_2722_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_2712_, v_n_2711_, v___x_2720_, v___x_2721_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg___boxed(lean_object* v_n_2723_, lean_object* v_f_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v_n_2723_, v_f_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v_n_2723_);
return v_res_2732_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2736_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__2));
v___x_2737_ = lean_unsigned_to_nat(2u);
v___x_2738_ = lean_unsigned_to_nat(113u);
v___x_2739_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__1));
v___x_2740_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__0));
v___x_2741_ = l_mkPanicMessageWithDecl(v___x_2740_, v___x_2739_, v___x_2738_, v___x_2737_, v___x_2736_);
return v___x_2741_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__8));
v___x_2753_ = l_String_toRawSubstring_x27(v___x_2752_);
return v___x_2753_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__20));
v___x_2779_ = l_String_toRawSubstring_x27(v___x_2778_);
return v___x_2779_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__27));
v___x_2794_ = l_String_toRawSubstring_x27(v___x_2793_);
return v___x_2794_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__33));
v___x_2808_ = l_String_toRawSubstring_x27(v___x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(lean_object* v_header_2817_, lean_object* v_indVal_2818_, lean_object* v_auxFunName_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v_targetNames_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_3022_; 
v_targetNames_2827_ = lean_ctor_get(v_header_2817_, 2);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_header_2817_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; lean_object* v_unused_3024_; lean_object* v_unused_3025_; 
v_unused_3023_ = lean_ctor_get(v_header_2817_, 3);
lean_dec(v_unused_3023_);
v_unused_3024_ = lean_ctor_get(v_header_2817_, 1);
lean_dec(v_unused_3024_);
v_unused_3025_ = lean_ctor_get(v_header_2817_, 0);
lean_dec(v_unused_3025_);
v___x_2829_ = v_header_2817_;
v_isShared_2830_ = v_isSharedCheck_3022_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_targetNames_2827_);
lean_dec(v_header_2817_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_3022_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; uint8_t v_rhs__empty_2833_; 
v___x_2831_ = lean_array_get_size(v_targetNames_2827_);
v___x_2832_ = lean_unsigned_to_nat(2u);
v_rhs__empty_2833_ = lean_nat_dec_eq(v___x_2831_, v___x_2832_);
if (v_rhs__empty_2833_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_del_object(v___x_2829_);
lean_dec_ref(v_targetNames_2827_);
lean_dec(v_auxFunName_2819_);
lean_dec_ref(v_indVal_2818_);
v___x_2834_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__3);
v___x_2835_ = l_panic___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__0(v___x_2834_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
return v___x_2835_;
}
else
{
lean_object* v_toConstantVal_2836_; lean_object* v_ctors_2837_; lean_object* v_name_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_3019_; 
v_toConstantVal_2836_ = lean_ctor_get(v_indVal_2818_, 0);
lean_inc_ref(v_toConstantVal_2836_);
v_ctors_2837_ = lean_ctor_get(v_indVal_2818_, 4);
v_name_2838_ = lean_ctor_get(v_toConstantVal_2836_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_toConstantVal_2836_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; lean_object* v_unused_3021_; 
v_unused_3020_ = lean_ctor_get(v_toConstantVal_2836_, 2);
lean_dec(v_unused_3020_);
v_unused_3021_ = lean_ctor_get(v_toConstantVal_2836_, 1);
lean_dec(v_unused_3021_);
v___x_2840_ = v_toConstantVal_2836_;
v_isShared_2841_ = v_isSharedCheck_3019_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_name_2838_);
lean_dec(v_toConstantVal_2836_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_3019_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v_ctorIdxName_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_inc_n(v_name_2838_, 2);
v_ctorIdxName_2842_ = l_Lean_mkCtorIdxName(v_name_2838_);
v___x_2843_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__5));
v___x_2844_ = l_Lean_Name_append(v_name_2838_, v___x_2843_);
v___x_2845_ = l_Lean_Core_mkFreshUserName(v___x_2844_, v_a_2824_, v_a_2825_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2847_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc_n(v_a_2846_, 2);
lean_dec_ref_known(v___x_2845_, 1);
lean_inc(v_name_2838_);
v___x_2847_ = l_Lean_mkCasesOnSameCtor(v_a_2846_, v_name_2838_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v___f_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___f_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec_ref_known(v___x_2847_, 1);
v___f_2848_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___closed__0));
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_box(v_rhs__empty_2833_);
lean_inc_ref(v_indVal_2818_);
lean_inc(v_ctors_2837_);
v___f_2851_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2851_, 0, v___x_2849_);
lean_closure_set(v___f_2851_, 1, v_ctors_2837_);
lean_closure_set(v___f_2851_, 2, v___x_2850_);
lean_closure_set(v___f_2851_, 3, v_indVal_2818_);
lean_closure_set(v___f_2851_, 4, v_name_2838_);
lean_closure_set(v___f_2851_, 5, v_auxFunName_2819_);
lean_closure_set(v___f_2851_, 6, v___f_2848_);
v___x_2852_ = l_Lean_InductiveVal_numCtors(v_indVal_2818_);
lean_dec_ref(v_indVal_2818_);
v___x_2853_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v___x_2852_, v___f_2851_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2994_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2994_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2994_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v_x1_2861_; lean_object* v___x_2862_; lean_object* v_x2_2863_; uint8_t v___x_2864_; 
v___x_2858_ = lean_unsigned_to_nat(1u);
v___x_2859_ = lean_unsigned_to_nat(0u);
v___x_2860_ = lean_array_get_borrowed(v___x_2849_, v_targetNames_2827_, v___x_2859_);
lean_inc(v___x_2860_);
v_x1_2861_ = l_Lean_mkIdent(v___x_2860_);
v___x_2862_ = lean_array_get(v___x_2849_, v_targetNames_2827_, v___x_2858_);
lean_dec_ref(v_targetNames_2827_);
v_x2_2863_ = l_Lean_mkIdent(v___x_2862_);
v___x_2864_ = lean_nat_dec_eq(v___x_2852_, v___x_2858_);
lean_dec(v___x_2852_);
if (v___x_2864_ == 0)
{
lean_object* v_toCold_2865_; lean_object* v_ref_2866_; lean_object* v_quotContext_2867_; lean_object* v_currMacroScope_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
v_toCold_2865_ = lean_ctor_get(v_a_2824_, 0);
v_ref_2866_ = lean_ctor_get(v_a_2824_, 2);
v_quotContext_2867_ = lean_ctor_get(v_toCold_2865_, 8);
v_currMacroScope_2868_ = lean_ctor_get(v_toCold_2865_, 9);
v___x_2869_ = l_Lean_SourceInfo_fromRef(v_ref_2866_, v___x_2864_);
v___x_2870_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__0));
v___x_2871_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__1));
lean_inc_n(v___x_2869_, 2);
v___x_2872_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2869_);
lean_ctor_set(v___x_2872_, 1, v___x_2870_);
v___x_2873_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2874_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
if (v_isShared_2841_ == 0)
{
lean_ctor_set_tag(v___x_2840_, 1);
lean_ctor_set(v___x_2840_, 2, v___x_2874_);
lean_ctor_set(v___x_2840_, 1, v___x_2873_);
lean_ctor_set(v___x_2840_, 0, v___x_2869_);
v___x_2876_ = v___x_2840_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2869_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2968_, 2, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2877_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__7));
v___x_2878_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2879_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__9);
v___x_2880_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__12));
lean_inc(v_currMacroScope_2868_);
lean_inc(v_quotContext_2867_);
v___x_2881_ = l_Lean_addMacroScope(v_quotContext_2867_, v___x_2880_, v_currMacroScope_2868_);
v___x_2882_ = lean_box(0);
v___x_2883_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__16));
lean_inc(v___x_2869_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set_tag(v___x_2829_, 3);
lean_ctor_set(v___x_2829_, 3, v___x_2883_);
lean_ctor_set(v___x_2829_, 2, v___x_2881_);
lean_ctor_set(v___x_2829_, 1, v___x_2879_);
lean_ctor_set(v___x_2829_, 0, v___x_2869_);
v___x_2885_ = v___x_2829_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2869_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v___x_2879_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2967_, 3, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2886_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__33));
v___x_2887_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__35));
v___x_2888_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
lean_inc_n(v___x_2869_, 41);
v___x_2889_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2869_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__38));
v___x_2891_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__40);
lean_inc_n(v_currMacroScope_2868_, 5);
lean_inc_n(v_quotContext_2867_, 5);
v___x_2892_ = l_Lean_addMacroScope(v_quotContext_2867_, v___x_2849_, v_currMacroScope_2868_);
v___x_2893_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___lam__1___closed__8));
v___x_2894_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2869_);
lean_ctor_set(v___x_2894_, 1, v___x_2891_);
lean_ctor_set(v___x_2894_, 2, v___x_2892_);
lean_ctor_set(v___x_2894_, 3, v___x_2893_);
v___x_2895_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2890_, v___x_2894_);
v___x_2896_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2887_, v___x_2889_, v___x_2895_);
v___x_2897_ = l_Lean_mkCIdent(v_ctorIdxName_2842_);
lean_inc(v_x1_2861_);
v___x_2898_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2873_, v_x1_2861_);
lean_inc(v___x_2897_);
v___x_2899_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2878_, v___x_2897_, v___x_2898_);
v___x_2900_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_2901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2869_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
lean_inc_ref(v___x_2901_);
lean_inc(v___x_2896_);
v___x_2902_ = l_Lean_Syntax_node3(v___x_2869_, v___x_2886_, v___x_2896_, v___x_2899_, v___x_2901_);
lean_inc(v_x2_2863_);
v___x_2903_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2873_, v_x2_2863_);
v___x_2904_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2878_, v___x_2897_, v___x_2903_);
v___x_2905_ = l_Lean_Syntax_node3(v___x_2869_, v___x_2886_, v___x_2896_, v___x_2904_, v___x_2901_);
v___x_2906_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2873_, v___x_2902_, v___x_2905_);
v___x_2907_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2878_, v___x_2885_, v___x_2906_);
lean_inc_ref_n(v___x_2876_, 2);
v___x_2908_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2877_, v___x_2876_, v___x_2907_);
v___x_2909_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2873_, v___x_2908_);
v___x_2910_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__2));
v___x_2911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2869_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld___closed__4));
v___x_2913_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__9));
v___x_2914_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__10));
v___x_2915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2869_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__18));
v___x_2917_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__19));
v___x_2918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2869_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__21);
v___x_2920_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__22));
v___x_2921_ = l_Lean_addMacroScope(v_quotContext_2867_, v___x_2920_, v_currMacroScope_2868_);
v___x_2922_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__26));
v___x_2923_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2869_);
lean_ctor_set(v___x_2923_, 1, v___x_2919_);
lean_ctor_set(v___x_2923_, 2, v___x_2921_);
lean_ctor_set(v___x_2923_, 3, v___x_2922_);
lean_inc_ref(v___x_2918_);
v___x_2924_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2916_, v___x_2918_, v___x_2923_);
v___x_2925_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__16);
v___x_2926_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__17));
v___x_2927_ = l_Lean_addMacroScope(v_quotContext_2867_, v___x_2926_, v_currMacroScope_2868_);
v___x_2928_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2869_);
lean_ctor_set(v___x_2928_, 1, v___x_2925_);
lean_ctor_set(v___x_2928_, 2, v___x_2927_);
lean_ctor_set(v___x_2928_, 3, v___x_2882_);
lean_inc_ref(v___x_2928_);
v___x_2929_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2873_, v___x_2928_);
v___x_2930_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2878_, v___x_2924_, v___x_2929_);
v___x_2931_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2873_, v___x_2930_);
v___x_2932_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2873_, v___x_2931_);
v___x_2933_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__16));
v___x_2934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2869_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = l_Lean_mkCIdent(v_a_2846_);
v___x_2936_ = l_Array_mkArray3___redArg(v_x1_2861_, v_x2_2863_, v___x_2928_);
v___x_2937_ = l_Array_append___redArg(v___x_2936_, v_a_2854_);
lean_dec(v_a_2854_);
v___x_2938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2869_);
lean_ctor_set(v___x_2938_, 1, v___x_2873_);
lean_ctor_set(v___x_2938_, 2, v___x_2937_);
v___x_2939_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2878_, v___x_2935_, v___x_2938_);
lean_inc_ref(v___x_2934_);
lean_inc_ref(v___x_2915_);
v___x_2940_ = l_Lean_Syntax_node4(v___x_2869_, v___x_2913_, v___x_2915_, v___x_2932_, v___x_2934_, v___x_2939_);
v___x_2941_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__28);
v___x_2942_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__29));
v___x_2943_ = l_Lean_addMacroScope(v_quotContext_2867_, v___x_2942_, v_currMacroScope_2868_);
v___x_2944_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__32));
v___x_2945_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2869_);
lean_ctor_set(v___x_2945_, 1, v___x_2941_);
lean_ctor_set(v___x_2945_, 2, v___x_2943_);
lean_ctor_set(v___x_2945_, 3, v___x_2944_);
v___x_2946_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2916_, v___x_2918_, v___x_2945_);
v___x_2947_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__3));
v___x_2948_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt_spec__1___redArg___closed__4));
v___x_2949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2869_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
v___x_2950_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2947_, v___x_2949_);
v___x_2951_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2873_, v___x_2950_);
v___x_2952_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2878_, v___x_2946_, v___x_2951_);
v___x_2953_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2873_, v___x_2952_);
v___x_2954_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2873_, v___x_2953_);
v___x_2955_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__2);
v___x_2956_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__3));
v___x_2957_ = l_Lean_addMacroScope(v_quotContext_2867_, v___x_2956_, v_currMacroScope_2868_);
v___x_2958_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__7));
v___x_2959_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2869_);
lean_ctor_set(v___x_2959_, 1, v___x_2955_);
lean_ctor_set(v___x_2959_, 2, v___x_2957_);
lean_ctor_set(v___x_2959_, 3, v___x_2958_);
v___x_2960_ = l_Lean_Syntax_node4(v___x_2869_, v___x_2913_, v___x_2915_, v___x_2954_, v___x_2934_, v___x_2959_);
v___x_2961_ = l_Lean_Syntax_node2(v___x_2869_, v___x_2873_, v___x_2940_, v___x_2960_);
v___x_2962_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2912_, v___x_2961_);
v___x_2963_ = l_Lean_Syntax_node6(v___x_2869_, v___x_2871_, v___x_2872_, v___x_2876_, v___x_2876_, v___x_2909_, v___x_2911_, v___x_2962_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2963_);
v___x_2965_ = v___x_2856_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v_toCold_2969_; lean_object* v_ref_2970_; lean_object* v_quotContext_2971_; lean_object* v_currMacroScope_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
lean_dec(v_ctorIdxName_2842_);
v_toCold_2969_ = lean_ctor_get(v_a_2824_, 0);
v_ref_2970_ = lean_ctor_get(v_a_2824_, 2);
v_quotContext_2971_ = lean_ctor_get(v_toCold_2969_, 8);
v_currMacroScope_2972_ = lean_ctor_get(v_toCold_2969_, 9);
v___x_2973_ = 0;
v___x_2974_ = l_Lean_SourceInfo_fromRef(v_ref_2970_, v___x_2973_);
v___x_2975_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__52));
v___x_2976_ = l_Lean_mkCIdent(v_a_2846_);
v___x_2977_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_2978_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__34);
v___x_2979_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__35));
lean_inc(v_currMacroScope_2972_);
lean_inc(v_quotContext_2971_);
v___x_2980_ = l_Lean_addMacroScope(v_quotContext_2971_, v___x_2979_, v_currMacroScope_2972_);
v___x_2981_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___closed__37));
lean_inc(v___x_2974_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set_tag(v___x_2829_, 3);
lean_ctor_set(v___x_2829_, 3, v___x_2981_);
lean_ctor_set(v___x_2829_, 2, v___x_2980_);
lean_ctor_set(v___x_2829_, 1, v___x_2978_);
lean_ctor_set(v___x_2829_, 0, v___x_2974_);
v___x_2983_ = v___x_2829_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2993_, 2, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_2993_, 3, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2984_ = l_Array_mkArray3___redArg(v_x1_2861_, v_x2_2863_, v___x_2983_);
v___x_2985_ = l_Array_append___redArg(v___x_2984_, v_a_2854_);
lean_dec(v_a_2854_);
lean_inc(v___x_2974_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set_tag(v___x_2840_, 1);
lean_ctor_set(v___x_2840_, 2, v___x_2985_);
lean_ctor_set(v___x_2840_, 1, v___x_2977_);
lean_ctor_set(v___x_2840_, 0, v___x_2974_);
v___x_2987_ = v___x_2840_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v___x_2977_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2988_ = l_Lean_Syntax_node2(v___x_2974_, v___x_2975_, v___x_2976_, v___x_2987_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2988_);
v___x_2990_ = v___x_2856_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v___x_2852_);
lean_dec(v_a_2846_);
lean_dec(v_ctorIdxName_2842_);
lean_del_object(v___x_2840_);
lean_del_object(v___x_2829_);
lean_dec_ref(v_targetNames_2827_);
v_a_2995_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2853_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2853_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_a_2846_);
lean_dec(v_ctorIdxName_2842_);
lean_del_object(v___x_2840_);
lean_dec(v_name_2838_);
lean_del_object(v___x_2829_);
lean_dec_ref(v_targetNames_2827_);
lean_dec(v_auxFunName_2819_);
lean_dec_ref(v_indVal_2818_);
v_a_3003_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2847_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2847_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec(v_ctorIdxName_2842_);
lean_del_object(v___x_2840_);
lean_dec(v_name_2838_);
lean_del_object(v___x_2829_);
lean_dec_ref(v_targetNames_2827_);
lean_dec(v_auxFunName_2819_);
lean_dec_ref(v_indVal_2818_);
v_a_3011_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2845_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2845_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew___boxed(lean_object* v_header_3026_, lean_object* v_indVal_3027_, lean_object* v_auxFunName_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(v_header_3026_, v_indVal_3027_, v_auxFunName_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1(lean_object* v___x_3037_, lean_object* v_as_3038_, size_t v_i_3039_, size_t v_stop_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___redArg(v___x_3037_, v_as_3038_, v_i_3039_, v_stop_3040_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1___boxed(lean_object* v___x_3049_, lean_object* v_as_3050_, lean_object* v_i_3051_, lean_object* v_stop_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
size_t v_i_boxed_3060_; size_t v_stop_boxed_3061_; lean_object* v_res_3062_; 
v_i_boxed_3060_ = lean_unbox_usize(v_i_3051_);
lean_dec(v_i_3051_);
v_stop_boxed_3061_ = lean_unbox_usize(v_stop_3052_);
lean_dec(v_stop_3052_);
v_res_3062_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__1(v___x_3049_, v_as_3050_, v_i_boxed_3060_, v_stop_boxed_3061_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec_ref(v_as_3050_);
lean_dec(v___x_3049_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2(lean_object* v_upperBound_3063_, lean_object* v_indVal_3064_, lean_object* v___x_3065_, lean_object* v_xs_3066_, lean_object* v_a_3067_, lean_object* v___x_3068_, lean_object* v_auxFunName_3069_, lean_object* v_inst_3070_, lean_object* v_R_3071_, lean_object* v_a_3072_, lean_object* v_b_3073_, lean_object* v_c_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___redArg(v_upperBound_3063_, v_indVal_3064_, v___x_3065_, v_xs_3066_, v_a_3067_, v___x_3068_, v_auxFunName_3069_, v_a_3072_, v_b_3073_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_3083_ = _args[0];
lean_object* v_indVal_3084_ = _args[1];
lean_object* v___x_3085_ = _args[2];
lean_object* v_xs_3086_ = _args[3];
lean_object* v_a_3087_ = _args[4];
lean_object* v___x_3088_ = _args[5];
lean_object* v_auxFunName_3089_ = _args[6];
lean_object* v_inst_3090_ = _args[7];
lean_object* v_R_3091_ = _args[8];
lean_object* v_a_3092_ = _args[9];
lean_object* v_b_3093_ = _args[10];
lean_object* v_c_3094_ = _args[11];
lean_object* v___y_3095_ = _args[12];
lean_object* v___y_3096_ = _args[13];
lean_object* v___y_3097_ = _args[14];
lean_object* v___y_3098_ = _args[15];
lean_object* v___y_3099_ = _args[16];
lean_object* v___y_3100_ = _args[17];
lean_object* v___y_3101_ = _args[18];
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__2(v_upperBound_3083_, v_indVal_3084_, v___x_3085_, v_xs_3086_, v_a_3087_, v___x_3088_, v_auxFunName_3089_, v_inst_3090_, v_R_3091_, v_a_3092_, v_b_3093_, v_c_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___x_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v___x_3085_);
lean_dec_ref(v_indVal_3084_);
lean_dec(v_upperBound_3083_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3(lean_object* v_00_u03b1_3103_, lean_object* v_n_3104_, lean_object* v_f_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v___x_3113_; 
v___x_3113_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___redArg(v_n_3104_, v_f_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3___boxed(lean_object* v_00_u03b1_3114_, lean_object* v_n_3115_, lean_object* v_f_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3(v_00_u03b1_3114_, v_n_3115_, v_f_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v_n_3115_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3(lean_object* v_00_u03b1_3125_, lean_object* v_f_3126_, lean_object* v_n_3127_, lean_object* v_x_3128_, lean_object* v_i_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___redArg(v_f_3126_, v_n_3127_, v_x_3128_, v_i_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3___boxed(lean_object* v_00_u03b1_3138_, lean_object* v_f_3139_, lean_object* v_n_3140_, lean_object* v_x_3141_, lean_object* v_i_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew_spec__3_spec__3(v_00_u03b1_3138_, v_f_3139_, v_n_3140_, v_x_3141_, v_i_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v_n_3140_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(lean_object* v_opts_3151_, lean_object* v_opt_3152_){
_start:
{
lean_object* v_name_3153_; lean_object* v_defValue_3154_; lean_object* v_map_3155_; lean_object* v___x_3156_; 
v_name_3153_ = lean_ctor_get(v_opt_3152_, 0);
v_defValue_3154_ = lean_ctor_get(v_opt_3152_, 1);
v_map_3155_ = lean_ctor_get(v_opts_3151_, 0);
v___x_3156_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3155_, v_name_3153_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_inc(v_defValue_3154_);
return v_defValue_3154_;
}
else
{
lean_object* v_val_3157_; 
v_val_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_val_3157_);
lean_dec_ref_known(v___x_3156_, 1);
if (lean_obj_tag(v_val_3157_) == 3)
{
lean_object* v_v_3158_; 
v_v_3158_ = lean_ctor_get(v_val_3157_, 0);
lean_inc(v_v_3158_);
lean_dec_ref_known(v_val_3157_, 1);
return v_v_3158_;
}
else
{
lean_dec(v_val_3157_);
lean_inc(v_defValue_3154_);
return v_defValue_3154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0___boxed(lean_object* v_opts_3159_, lean_object* v_opt_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(v_opts_3159_, v_opt_3160_);
lean_dec_ref(v_opt_3160_);
lean_dec_ref(v_opts_3159_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(lean_object* v_header_3162_, lean_object* v_indVal_3163_, lean_object* v_auxFunName_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v_toCold_3172_; lean_object* v_options_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v_toCold_3172_ = lean_ctor_get(v_a_3169_, 0);
v_options_3173_ = lean_ctor_get(v_toCold_3172_, 2);
v___x_3174_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_deriving_beq_linear__construction__threshold;
v___x_3175_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch_spec__0(v_options_3173_, v___x_3174_);
v___x_3176_ = l_Lean_InductiveVal_numCtors(v_indVal_3163_);
v___x_3177_ = lean_nat_dec_le(v___x_3175_, v___x_3176_);
lean_dec(v___x_3176_);
lean_dec(v___x_3175_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; 
v___x_3178_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld(v_header_3162_, v_indVal_3163_, v_auxFunName_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
return v___x_3178_;
}
else
{
lean_object* v___x_3179_; 
v___x_3179_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchNew(v_header_3162_, v_indVal_3163_, v_auxFunName_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
return v___x_3179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch___boxed(lean_object* v_header_3180_, lean_object* v_indVal_3181_, lean_object* v_auxFunName_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(v_header_3180_, v_indVal_3181_, v_auxFunName_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
return v_res_3190_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__4));
v___x_3230_ = l_String_toRawSubstring_x27(v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(lean_object* v_ctx_3267_, lean_object* v_i_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_){
_start:
{
lean_object* v_typeInfos_3276_; lean_object* v_auxFunNames_3277_; uint8_t v_usePartial_3278_; lean_object* v___x_3279_; lean_object* v_indVal_3280_; lean_object* v___x_3281_; 
v_typeInfos_3276_ = lean_ctor_get(v_ctx_3267_, 1);
v_auxFunNames_3277_ = lean_ctor_get(v_ctx_3267_, 2);
v_usePartial_3278_ = lean_ctor_get_uint8(v_ctx_3267_, sizeof(void*)*3);
v___x_3279_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_3280_ = lean_array_get_borrowed(v___x_3279_, v_typeInfos_3276_, v_i_3268_);
lean_inc(v_indVal_3280_);
v___x_3281_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader(v_indVal_3280_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3418_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3284_ = v___x_3281_;
v_isShared_3285_ = v_isSharedCheck_3418_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3418_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v_auxFunName_3287_; lean_object* v_body_3289_; lean_object* v___y_3290_; lean_object* v___x_3401_; 
v___x_3286_ = lean_box(0);
v_auxFunName_3287_ = lean_array_get_borrowed(v___x_3286_, v_auxFunNames_3277_, v_i_3268_);
lean_inc(v_auxFunName_3287_);
lean_inc(v_indVal_3280_);
lean_inc(v_a_3282_);
v___x_3401_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatch(v_a_3282_, v_indVal_3280_, v_auxFunName_3287_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_);
if (lean_obj_tag(v___x_3401_) == 0)
{
if (v_usePartial_3278_ == 0)
{
lean_object* v_a_3402_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3401_, 1);
v_body_3289_ = v_a_3402_;
v___y_3290_ = v_a_3273_;
goto v___jp_3288_;
}
else
{
lean_object* v_a_3403_; lean_object* v_argNames_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v_a_3403_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3401_, 1);
v_argNames_3404_ = lean_ctor_get(v_a_3282_, 1);
v___x_3405_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
lean_inc_ref(v_argNames_3404_);
v___x_3406_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_3267_, v___x_3405_, v_argNames_3404_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3408_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3406_, 1);
v___x_3408_ = l_Lean_Elab_Deriving_mkLet(v_a_3407_, v_a_3403_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_);
lean_dec(v_a_3407_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3408_, 1);
v_body_3289_ = v_a_3409_;
v___y_3290_ = v_a_3273_;
goto v___jp_3288_;
}
else
{
lean_del_object(v___x_3284_);
lean_dec(v_a_3282_);
return v___x_3408_;
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v_a_3403_);
lean_del_object(v___x_3284_);
lean_dec(v_a_3282_);
v_a_3410_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3406_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3406_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
}
else
{
lean_del_object(v___x_3284_);
lean_dec(v_a_3282_);
return v___x_3401_;
}
v___jp_3288_:
{
if (v_usePartial_3278_ == 0)
{
lean_object* v_toCold_3291_; lean_object* v_binders_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3339_; 
v_toCold_3291_ = lean_ctor_get(v___y_3290_, 0);
v_binders_3292_ = lean_ctor_get(v_a_3282_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_a_3282_);
if (v_isSharedCheck_3339_ == 0)
{
lean_object* v_unused_3340_; lean_object* v_unused_3341_; lean_object* v_unused_3342_; 
v_unused_3340_ = lean_ctor_get(v_a_3282_, 3);
lean_dec(v_unused_3340_);
v_unused_3341_ = lean_ctor_get(v_a_3282_, 2);
lean_dec(v_unused_3341_);
v_unused_3342_ = lean_ctor_get(v_a_3282_, 1);
lean_dec(v_unused_3342_);
v___x_3294_ = v_a_3282_;
v_isShared_3295_ = v_isSharedCheck_3339_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_binders_3292_);
lean_dec(v_a_3282_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3339_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v_ref_3296_; lean_object* v_quotContext_3297_; lean_object* v_currMacroScope_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3323_; 
v_ref_3296_ = lean_ctor_get(v___y_3290_, 2);
v_quotContext_3297_ = lean_ctor_get(v_toCold_3291_, 8);
v_currMacroScope_3298_ = lean_ctor_get(v_toCold_3291_, 9);
v___x_3299_ = l_Lean_SourceInfo_fromRef(v_ref_3296_, v_usePartial_3278_);
v___x_3300_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3301_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3302_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3303_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3299_, 7);
v___x_3304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3299_);
lean_ctor_set(v___x_3304_, 1, v___x_3302_);
lean_ctor_set(v___x_3304_, 2, v___x_3303_);
lean_inc_ref_n(v___x_3304_, 8);
v___x_3305_ = l_Lean_Syntax_node7(v___x_3299_, v___x_3301_, v___x_3304_, v___x_3304_, v___x_3304_, v___x_3304_, v___x_3304_, v___x_3304_, v___x_3304_);
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3307_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3299_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3287_);
v___x_3310_ = l_Lean_mkIdent(v_auxFunName_3287_);
v___x_3311_ = l_Lean_Syntax_node2(v___x_3299_, v___x_3309_, v___x_3310_, v___x_3304_);
v___x_3312_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3313_ = l_Array_append___redArg(v___x_3303_, v_binders_3292_);
lean_dec_ref(v_binders_3292_);
v___x_3314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3299_);
lean_ctor_set(v___x_3314_, 1, v___x_3302_);
lean_ctor_set(v___x_3314_, 2, v___x_3313_);
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3316_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3299_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
v___x_3318_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3319_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_3298_);
lean_inc(v_quotContext_3297_);
v___x_3320_ = l_Lean_addMacroScope(v_quotContext_3297_, v___x_3319_, v_currMacroScope_3298_);
v___x_3321_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20));
if (v_isShared_3295_ == 0)
{
lean_ctor_set_tag(v___x_3294_, 3);
lean_ctor_set(v___x_3294_, 3, v___x_3321_);
lean_ctor_set(v___x_3294_, 2, v___x_3320_);
lean_ctor_set(v___x_3294_, 1, v___x_3318_);
lean_ctor_set(v___x_3294_, 0, v___x_3299_);
v___x_3323_ = v___x_3294_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v___x_3318_);
lean_ctor_set(v_reuseFailAlloc_3338_, 2, v___x_3320_);
lean_ctor_set(v_reuseFailAlloc_3338_, 3, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
lean_inc_n(v___x_3299_, 7);
v___x_3324_ = l_Lean_Syntax_node2(v___x_3299_, v___x_3315_, v___x_3317_, v___x_3323_);
v___x_3325_ = l_Lean_Syntax_node1(v___x_3299_, v___x_3302_, v___x_3324_);
v___x_3326_ = l_Lean_Syntax_node2(v___x_3299_, v___x_3312_, v___x_3314_, v___x_3325_);
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3328_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23));
v___x_3329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3299_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26));
lean_inc_ref_n(v___x_3304_, 3);
v___x_3331_ = l_Lean_Syntax_node2(v___x_3299_, v___x_3330_, v___x_3304_, v___x_3304_);
v___x_3332_ = l_Lean_Syntax_node4(v___x_3299_, v___x_3327_, v___x_3329_, v_body_3289_, v___x_3331_, v___x_3304_);
v___x_3333_ = l_Lean_Syntax_node5(v___x_3299_, v___x_3306_, v___x_3308_, v___x_3311_, v___x_3326_, v___x_3332_, v___x_3304_);
v___x_3334_ = l_Lean_Syntax_node2(v___x_3299_, v___x_3300_, v___x_3305_, v___x_3333_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3334_);
v___x_3336_ = v___x_3284_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
else
{
lean_object* v_toCold_3343_; lean_object* v_binders_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3397_; 
v_toCold_3343_ = lean_ctor_get(v___y_3290_, 0);
v_binders_3344_ = lean_ctor_get(v_a_3282_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_a_3282_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; lean_object* v_unused_3399_; lean_object* v_unused_3400_; 
v_unused_3398_ = lean_ctor_get(v_a_3282_, 3);
lean_dec(v_unused_3398_);
v_unused_3399_ = lean_ctor_get(v_a_3282_, 2);
lean_dec(v_unused_3399_);
v_unused_3400_ = lean_ctor_get(v_a_3282_, 1);
lean_dec(v_unused_3400_);
v___x_3346_ = v_a_3282_;
v_isShared_3347_ = v_isSharedCheck_3397_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_binders_3344_);
lean_dec(v_a_3282_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3397_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v_ref_3348_; lean_object* v_quotContext_3349_; lean_object* v_currMacroScope_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3381_; 
v_ref_3348_ = lean_ctor_get(v___y_3290_, 2);
v_quotContext_3349_ = lean_ctor_get(v_toCold_3343_, 8);
v_currMacroScope_3350_ = lean_ctor_get(v_toCold_3343_, 9);
v___x_3351_ = 0;
v___x_3352_ = l_Lean_SourceInfo_fromRef(v_ref_3348_, v___x_3351_);
v___x_3353_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3354_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3355_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3356_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3352_, 10);
v___x_3357_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3352_);
lean_ctor_set(v___x_3357_, 1, v___x_3355_);
lean_ctor_set(v___x_3357_, 2, v___x_3356_);
v___x_3358_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__27));
v___x_3359_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__28));
v___x_3360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3352_);
lean_ctor_set(v___x_3360_, 1, v___x_3358_);
v___x_3361_ = l_Lean_Syntax_node1(v___x_3352_, v___x_3359_, v___x_3360_);
v___x_3362_ = l_Lean_Syntax_node1(v___x_3352_, v___x_3355_, v___x_3361_);
lean_inc_ref_n(v___x_3357_, 7);
v___x_3363_ = l_Lean_Syntax_node7(v___x_3352_, v___x_3354_, v___x_3357_, v___x_3357_, v___x_3357_, v___x_3357_, v___x_3357_, v___x_3357_, v___x_3362_);
v___x_3364_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3365_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3352_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3287_);
v___x_3368_ = l_Lean_mkIdent(v_auxFunName_3287_);
v___x_3369_ = l_Lean_Syntax_node2(v___x_3352_, v___x_3367_, v___x_3368_, v___x_3357_);
v___x_3370_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3371_ = l_Array_append___redArg(v___x_3356_, v_binders_3344_);
lean_dec_ref(v_binders_3344_);
v___x_3372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3352_);
lean_ctor_set(v___x_3372_, 1, v___x_3355_);
lean_ctor_set(v___x_3372_, 2, v___x_3371_);
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3374_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3352_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3377_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_3350_);
lean_inc(v_quotContext_3349_);
v___x_3378_ = l_Lean_addMacroScope(v_quotContext_3349_, v___x_3377_, v_currMacroScope_3350_);
v___x_3379_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__20));
if (v_isShared_3347_ == 0)
{
lean_ctor_set_tag(v___x_3346_, 3);
lean_ctor_set(v___x_3346_, 3, v___x_3379_);
lean_ctor_set(v___x_3346_, 2, v___x_3378_);
lean_ctor_set(v___x_3346_, 1, v___x_3376_);
lean_ctor_set(v___x_3346_, 0, v___x_3352_);
v___x_3381_ = v___x_3346_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3352_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3396_, 2, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3396_, 3, v___x_3379_);
v___x_3381_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
lean_inc_n(v___x_3352_, 7);
v___x_3382_ = l_Lean_Syntax_node2(v___x_3352_, v___x_3373_, v___x_3375_, v___x_3381_);
v___x_3383_ = l_Lean_Syntax_node1(v___x_3352_, v___x_3355_, v___x_3382_);
v___x_3384_ = l_Lean_Syntax_node2(v___x_3352_, v___x_3370_, v___x_3372_, v___x_3383_);
v___x_3385_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3386_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23));
v___x_3387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3352_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26));
lean_inc_ref_n(v___x_3357_, 3);
v___x_3389_ = l_Lean_Syntax_node2(v___x_3352_, v___x_3388_, v___x_3357_, v___x_3357_);
v___x_3390_ = l_Lean_Syntax_node4(v___x_3352_, v___x_3385_, v___x_3387_, v_body_3289_, v___x_3389_, v___x_3357_);
v___x_3391_ = l_Lean_Syntax_node5(v___x_3352_, v___x_3364_, v___x_3366_, v___x_3369_, v___x_3384_, v___x_3390_, v___x_3357_);
v___x_3392_ = l_Lean_Syntax_node2(v___x_3352_, v___x_3353_, v___x_3363_, v___x_3391_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3392_);
v___x_3394_ = v___x_3284_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
v_a_3419_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3281_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3281_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___boxed(lean_object* v_ctx_3427_, lean_object* v_i_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(v_ctx_3427_, v_i_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
lean_dec(v_a_3432_);
lean_dec_ref(v_a_3431_);
lean_dec(v_a_3430_);
lean_dec_ref(v_a_3429_);
lean_dec(v_i_3428_);
lean_dec_ref(v_ctx_3427_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_3437_, lean_object* v_ctx_3438_, lean_object* v_a_3439_, lean_object* v_b_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
uint8_t v___x_3448_; 
v___x_3448_ = lean_nat_dec_lt(v_a_3439_, v_upperBound_3437_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3449_; 
lean_dec(v_a_3439_);
v___x_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3449_, 0, v_b_3440_);
return v___x_3449_;
}
else
{
lean_object* v___x_3450_; 
v___x_3450_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction(v_ctx_3438_, v_a_3439_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v___x_3452_ = lean_array_push(v_b_3440_, v_a_3451_);
v___x_3453_ = lean_unsigned_to_nat(1u);
v___x_3454_ = lean_nat_add(v_a_3439_, v___x_3453_);
lean_dec(v_a_3439_);
v_a_3439_ = v___x_3454_;
v_b_3440_ = v___x_3452_;
goto _start;
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec_ref(v_b_3440_);
lean_dec(v_a_3439_);
v_a_3456_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3450_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3450_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_3464_, lean_object* v_ctx_3465_, lean_object* v_a_3466_, lean_object* v_b_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v_upperBound_3464_, v_ctx_3465_, v_a_3466_, v_b_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec_ref(v_ctx_3465_);
lean_dec(v_upperBound_3464_);
return v_res_3475_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__4));
v___x_3490_ = l_String_toRawSubstring_x27(v___x_3489_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(lean_object* v_ctx_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_){
_start:
{
lean_object* v_typeInfos_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v_auxDefs_3516_; lean_object* v___x_3517_; 
v_typeInfos_3513_ = lean_ctor_get(v_ctx_3505_, 1);
v___x_3514_ = lean_array_get_size(v_typeInfos_3513_);
v___x_3515_ = lean_unsigned_to_nat(0u);
v_auxDefs_3516_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__0));
v___x_3517_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v___x_3514_, v_ctx_3505_, v___x_3515_, v_auxDefs_3516_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_toCold_3518_; lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3554_; 
v_toCold_3518_ = lean_ctor_get(v_a_3510_, 0);
v_a_3519_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3521_ = v___x_3517_;
v_isShared_3522_ = v_isSharedCheck_3554_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3517_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3554_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v_ref_3523_; lean_object* v_quotContext_3524_; lean_object* v_currMacroScope_3525_; uint8_t v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v_ref_3523_ = lean_ctor_get(v_a_3510_, 2);
v_quotContext_3524_ = lean_ctor_get(v_toCold_3518_, 8);
v_currMacroScope_3525_ = lean_ctor_get(v_toCold_3518_, 9);
v___x_3526_ = 0;
v___x_3527_ = l_Lean_SourceInfo_fromRef(v_ref_3523_, v___x_3526_);
v___x_3528_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__0));
v___x_3529_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__1));
lean_inc_n(v___x_3527_, 8);
v___x_3530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3527_);
lean_ctor_set(v___x_3530_, 1, v___x_3528_);
v___x_3531_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3532_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__2));
v___x_3533_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__3));
v___x_3534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3527_);
lean_ctor_set(v___x_3534_, 1, v___x_3532_);
v___x_3535_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__5);
v___x_3536_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__7));
lean_inc(v_currMacroScope_3525_);
lean_inc(v_quotContext_3524_);
v___x_3537_ = l_Lean_addMacroScope(v_quotContext_3524_, v___x_3536_, v_currMacroScope_3525_);
v___x_3538_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__10));
v___x_3539_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3527_);
lean_ctor_set(v___x_3539_, 1, v___x_3535_);
lean_ctor_set(v___x_3539_, 2, v___x_3537_);
lean_ctor_set(v___x_3539_, 3, v___x_3538_);
v___x_3540_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_3541_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3527_);
lean_ctor_set(v___x_3541_, 1, v___x_3531_);
lean_ctor_set(v___x_3541_, 2, v___x_3540_);
v___x_3542_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__5___redArg___lam__1___closed__0));
v___x_3543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3527_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = l_Lean_Syntax_node4(v___x_3527_, v___x_3533_, v___x_3534_, v___x_3539_, v___x_3541_, v___x_3543_);
v___x_3545_ = l_Array_mkArray1___redArg(v___x_3544_);
v___x_3546_ = l_Array_append___redArg(v___x_3545_, v_a_3519_);
lean_dec(v_a_3519_);
v___x_3547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3527_);
lean_ctor_set(v___x_3547_, 1, v___x_3531_);
lean_ctor_set(v___x_3547_, 2, v___x_3546_);
v___x_3548_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___closed__11));
v___x_3549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3527_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = l_Lean_Syntax_node3(v___x_3527_, v___x_3529_, v___x_3530_, v___x_3547_, v___x_3549_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3550_);
v___x_3552_ = v___x_3521_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
v_a_3555_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3517_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3517_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock___boxed(lean_object* v_ctx_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(v_ctx_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec_ref(v_ctx_3563_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0(lean_object* v_upperBound_3572_, lean_object* v_ctx_3573_, lean_object* v_inst_3574_, lean_object* v_R_3575_, lean_object* v_a_3576_, lean_object* v_b_3577_, lean_object* v_c_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___redArg(v_upperBound_3572_, v_ctx_3573_, v_a_3576_, v_b_3577_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_3587_, lean_object* v_ctx_3588_, lean_object* v_inst_3589_, lean_object* v_R_3590_, lean_object* v_a_3591_, lean_object* v_b_3592_, lean_object* v_c_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock_spec__0(v_upperBound_3587_, v_ctx_3588_, v_inst_3589_, v_R_3590_, v_a_3591_, v_b_3592_, v_c_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v_ctx_3588_);
lean_dec(v_upperBound_3587_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
if (lean_obj_tag(v_a_3602_) == 0)
{
lean_object* v___x_3604_; 
v___x_3604_ = l_List_reverse___redArg(v_a_3603_);
return v___x_3604_;
}
else
{
lean_object* v_head_3605_; lean_object* v_tail_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3615_; 
v_head_3605_ = lean_ctor_get(v_a_3602_, 0);
v_tail_3606_ = lean_ctor_get(v_a_3602_, 1);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_a_3602_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3608_ = v_a_3602_;
v_isShared_3609_ = v_isSharedCheck_3615_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_tail_3606_);
lean_inc(v_head_3605_);
lean_dec(v_a_3602_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3615_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3610_ = l_Lean_MessageData_ofSyntax(v_head_3605_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 1, v_a_3603_);
lean_ctor_set(v___x_3608_, 0, v___x_3610_);
v___x_3612_ = v___x_3608_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_a_3603_);
v___x_3612_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
v_a_3602_ = v_tail_3606_;
v_a_3603_ = v___x_3612_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3616_; double v___x_3617_; 
v___x_3616_ = lean_unsigned_to_nat(0u);
v___x_3617_ = lean_float_of_nat(v___x_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(lean_object* v_cls_3620_, lean_object* v_msg_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_ref_3627_; lean_object* v___x_3628_; lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3673_; 
v_ref_3627_ = lean_ctor_get(v___y_3624_, 2);
v___x_3628_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3631_ = v___x_3628_;
v_isShared_3632_ = v_isSharedCheck_3673_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3628_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3673_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v_traceState_3634_; lean_object* v_env_3635_; lean_object* v_nextMacroScope_3636_; lean_object* v_ngen_3637_; lean_object* v_auxDeclNGen_3638_; lean_object* v_cache_3639_; lean_object* v_messages_3640_; lean_object* v_infoState_3641_; lean_object* v_snapshotTasks_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3672_; 
v___x_3633_ = lean_st_ref_take(v___y_3625_);
v_traceState_3634_ = lean_ctor_get(v___x_3633_, 4);
v_env_3635_ = lean_ctor_get(v___x_3633_, 0);
v_nextMacroScope_3636_ = lean_ctor_get(v___x_3633_, 1);
v_ngen_3637_ = lean_ctor_get(v___x_3633_, 2);
v_auxDeclNGen_3638_ = lean_ctor_get(v___x_3633_, 3);
v_cache_3639_ = lean_ctor_get(v___x_3633_, 5);
v_messages_3640_ = lean_ctor_get(v___x_3633_, 6);
v_infoState_3641_ = lean_ctor_get(v___x_3633_, 7);
v_snapshotTasks_3642_ = lean_ctor_get(v___x_3633_, 8);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3644_ = v___x_3633_;
v_isShared_3645_ = v_isSharedCheck_3672_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_snapshotTasks_3642_);
lean_inc(v_infoState_3641_);
lean_inc(v_messages_3640_);
lean_inc(v_cache_3639_);
lean_inc(v_traceState_3634_);
lean_inc(v_auxDeclNGen_3638_);
lean_inc(v_ngen_3637_);
lean_inc(v_nextMacroScope_3636_);
lean_inc(v_env_3635_);
lean_dec(v___x_3633_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3672_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
uint64_t v_tid_3646_; lean_object* v_traces_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3671_; 
v_tid_3646_ = lean_ctor_get_uint64(v_traceState_3634_, sizeof(void*)*1);
v_traces_3647_ = lean_ctor_get(v_traceState_3634_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v_traceState_3634_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3649_ = v_traceState_3634_;
v_isShared_3650_ = v_isSharedCheck_3671_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_traces_3647_);
lean_dec(v_traceState_3634_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3671_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3651_; double v___x_3652_; uint8_t v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3651_ = lean_box(0);
v___x_3652_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__0);
v___x_3653_ = 0;
v___x_3654_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__39));
v___x_3655_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3655_, 0, v_cls_3620_);
lean_ctor_set(v___x_3655_, 1, v___x_3651_);
lean_ctor_set(v___x_3655_, 2, v___x_3654_);
lean_ctor_set_float(v___x_3655_, sizeof(void*)*3, v___x_3652_);
lean_ctor_set_float(v___x_3655_, sizeof(void*)*3 + 8, v___x_3652_);
lean_ctor_set_uint8(v___x_3655_, sizeof(void*)*3 + 16, v___x_3653_);
v___x_3656_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___closed__1));
v___x_3657_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v_a_3629_);
lean_ctor_set(v___x_3657_, 2, v___x_3656_);
lean_inc(v_ref_3627_);
v___x_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3658_, 0, v_ref_3627_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = l_Lean_PersistentArray_push___redArg(v_traces_3647_, v___x_3658_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 0, v___x_3659_);
v___x_3661_ = v___x_3649_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3659_);
lean_ctor_set_uint64(v_reuseFailAlloc_3670_, sizeof(void*)*1, v_tid_3646_);
v___x_3661_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3663_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 4, v___x_3661_);
v___x_3663_ = v___x_3644_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_env_3635_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_nextMacroScope_3636_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_ngen_3637_);
lean_ctor_set(v_reuseFailAlloc_3669_, 3, v_auxDeclNGen_3638_);
lean_ctor_set(v_reuseFailAlloc_3669_, 4, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3669_, 5, v_cache_3639_);
lean_ctor_set(v_reuseFailAlloc_3669_, 6, v_messages_3640_);
lean_ctor_set(v_reuseFailAlloc_3669_, 7, v_infoState_3641_);
lean_ctor_set(v_reuseFailAlloc_3669_, 8, v_snapshotTasks_3642_);
v___x_3663_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3667_; 
v___x_3664_ = lean_st_ref_put(v___y_3625_, v___x_3663_);
v___x_3665_ = lean_box(0);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v___x_3665_);
v___x_3667_ = v___x_3631_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_3674_, lean_object* v_msg_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v_cls_3674_, v_msg_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
return v_res_3681_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3689_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3690_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__2));
v___x_3691_ = l_Lean_Name_append(v___x_3690_, v___x_3689_);
return v___x_3691_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5(void){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__4));
v___x_3694_ = l_Lean_stringToMessageData(v___x_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(lean_object* v_ctx_3695_, lean_object* v_declName_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMutualBlock(v_ctx_3695_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; lean_object* v___x_3711_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
v___x_3706_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_3707_ = lean_unsigned_to_nat(1u);
v___x_3708_ = lean_mk_empty_array_with_capacity(v___x_3707_);
lean_inc_ref(v___x_3708_);
v___x_3709_ = lean_array_push(v___x_3708_, v_declName_3696_);
v___x_3710_ = 1;
v___x_3711_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_3695_, v___x_3706_, v___x_3709_, v___x_3710_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
lean_dec_ref(v___x_3709_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_toCold_3712_; lean_object* v_options_3713_; lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3754_; 
v_toCold_3712_ = lean_ctor_get(v_a_3701_, 0);
v_options_3713_ = lean_ctor_get(v_toCold_3712_, 2);
v_a_3714_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3716_ = v___x_3711_;
v_isShared_3717_ = v_isSharedCheck_3754_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3711_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3754_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v_inheritedTraceOptions_3718_; uint8_t v_hasTrace_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v_inheritedTraceOptions_3718_ = lean_ctor_get(v_toCold_3712_, 11);
v_hasTrace_3719_ = lean_ctor_get_uint8(v_options_3713_, sizeof(void*)*1);
v___x_3720_ = lean_array_push(v___x_3708_, v_a_3705_);
v___x_3721_ = l_Array_append___redArg(v___x_3720_, v_a_3714_);
lean_dec(v_a_3714_);
if (v_hasTrace_3719_ == 0)
{
lean_object* v___x_3723_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3721_);
v___x_3723_ = v___x_3716_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; 
v___x_3725_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3726_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3);
v___x_3727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3718_, v_options_3713_, v___x_3726_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3729_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3721_);
v___x_3729_ = v___x_3716_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3721_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_del_object(v___x_3716_);
v___x_3731_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5);
lean_inc_ref(v___x_3721_);
v___x_3732_ = lean_array_to_list(v___x_3721_);
v___x_3733_ = lean_box(0);
v___x_3734_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(v___x_3732_, v___x_3733_);
v___x_3735_ = l_Lean_MessageData_ofList(v___x_3734_);
v___x_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3731_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v___x_3725_, v___x_3736_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3744_ == 0)
{
lean_object* v_unused_3745_; 
v_unused_3745_ = lean_ctor_get(v___x_3737_, 0);
lean_dec(v_unused_3745_);
v___x_3739_ = v___x_3737_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_dec(v___x_3737_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v___x_3721_);
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3721_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec_ref(v___x_3721_);
v_a_3746_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3737_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3737_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec_ref(v___x_3708_);
lean_dec(v_a_3705_);
v_a_3755_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3711_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3711_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec(v_declName_3696_);
lean_dec_ref(v_ctx_3695_);
v_a_3763_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3704_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3704_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___boxed(lean_object* v_ctx_3771_, lean_object* v_declName_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(v_ctx_3771_, v_declName_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1(lean_object* v_cls_3781_, lean_object* v_msg_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v_cls_3781_, v_msg_3782_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___boxed(lean_object* v_cls_3791_, lean_object* v_msg_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1(v_cls_3791_, v_msg_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
return v_res_3800_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__2));
v___x_3809_ = l_String_toRawSubstring_x27(v___x_3808_);
return v___x_3809_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6(void){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__5));
v___x_3814_ = l_String_toRawSubstring_x27(v___x_3813_);
return v___x_3814_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12(void){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3827_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__11));
v___x_3828_ = l_String_toRawSubstring_x27(v___x_3827_);
return v___x_3828_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__15));
v___x_3835_ = l_String_toRawSubstring_x27(v___x_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(lean_object* v_ctx_3839_, lean_object* v_name_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v_toCold_3843_; lean_object* v_auxFunNames_3844_; lean_object* v_ref_3845_; lean_object* v_quotContext_3846_; lean_object* v_currMacroScope_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v_auxFunName_3850_; uint8_t v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_toCold_3843_ = lean_ctor_get(v_a_3841_, 0);
v_auxFunNames_3844_ = lean_ctor_get(v_ctx_3839_, 2);
v_ref_3845_ = lean_ctor_get(v_a_3841_, 2);
v_quotContext_3846_ = lean_ctor_get(v_toCold_3843_, 8);
v_currMacroScope_3847_ = lean_ctor_get(v_toCold_3843_, 9);
v___x_3848_ = lean_box(0);
v___x_3849_ = lean_unsigned_to_nat(0u);
v_auxFunName_3850_ = lean_array_get_borrowed(v___x_3848_, v_auxFunNames_3844_, v___x_3849_);
v___x_3851_ = 0;
v___x_3852_ = l_Lean_SourceInfo_fromRef(v_ref_3845_, v___x_3851_);
v___x_3853_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__2));
v___x_3854_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__4));
v___x_3855_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_3856_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
lean_inc_n(v___x_3852_, 25);
v___x_3857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3852_);
lean_ctor_set(v___x_3857_, 1, v___x_3855_);
lean_ctor_set(v___x_3857_, 2, v___x_3856_);
lean_inc_ref_n(v___x_3857_, 12);
v___x_3858_ = l_Lean_Syntax_node7(v___x_3852_, v___x_3854_, v___x_3857_, v___x_3857_, v___x_3857_, v___x_3857_, v___x_3857_, v___x_3857_, v___x_3857_);
v___x_3859_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__6));
v___x_3860_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__7));
v___x_3861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3852_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
v___x_3862_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3850_);
v___x_3863_ = l_Lean_mkIdent(v_auxFunName_3850_);
v___x_3864_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3862_, v___x_3863_, v___x_3857_);
v___x_3865_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__11));
v___x_3866_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__1));
v___x_3867_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__36));
v___x_3868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3852_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__3);
v___x_3870_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__4));
lean_inc_n(v_currMacroScope_3847_, 5);
lean_inc_n(v_quotContext_3846_, 5);
v___x_3871_ = l_Lean_addMacroScope(v_quotContext_3846_, v___x_3870_, v_currMacroScope_3847_);
v___x_3872_ = lean_box(0);
v___x_3873_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3852_);
lean_ctor_set(v___x_3873_, 1, v___x_3869_);
lean_ctor_set(v___x_3873_, 2, v___x_3871_);
lean_ctor_set(v___x_3873_, 3, v___x_3872_);
v___x_3874_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__6);
v___x_3875_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__7));
v___x_3876_ = l_Lean_addMacroScope(v_quotContext_3846_, v___x_3875_, v_currMacroScope_3847_);
v___x_3877_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3852_);
lean_ctor_set(v___x_3877_, 1, v___x_3874_);
lean_ctor_set(v___x_3877_, 2, v___x_3876_);
lean_ctor_set(v___x_3877_, 3, v___x_3872_);
v___x_3878_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3855_, v___x_3873_, v___x_3877_);
v___x_3879_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__18));
v___x_3880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3852_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
v___x_3881_ = l_Lean_mkCIdent(v_name_3840_);
lean_inc_ref(v___x_3880_);
v___x_3882_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3855_, v___x_3880_, v___x_3881_);
v___x_3883_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__60));
v___x_3884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3852_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = l_Lean_Syntax_node5(v___x_3852_, v___x_3866_, v___x_3868_, v___x_3878_, v___x_3882_, v___x_3857_, v___x_3884_);
v___x_3886_ = l_Lean_Syntax_node1(v___x_3852_, v___x_3855_, v___x_3885_);
v___x_3887_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__13));
v___x_3888_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__14);
v___x_3889_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__15));
v___x_3890_ = l_Lean_addMacroScope(v_quotContext_3846_, v___x_3889_, v_currMacroScope_3847_);
v___x_3891_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__10));
v___x_3892_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3852_);
lean_ctor_set(v___x_3892_, 1, v___x_3888_);
lean_ctor_set(v___x_3892_, 2, v___x_3890_);
lean_ctor_set(v___x_3892_, 3, v___x_3891_);
v___x_3893_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3887_, v___x_3880_, v___x_3892_);
v___x_3894_ = l_Lean_Syntax_node1(v___x_3852_, v___x_3855_, v___x_3893_);
v___x_3895_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3865_, v___x_3886_, v___x_3894_);
v___x_3896_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__22));
v___x_3897_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__23));
v___x_3898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3852_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__7));
v___x_3900_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__12);
v___x_3901_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__14));
v___x_3902_ = l_Lean_addMacroScope(v_quotContext_3846_, v___x_3901_, v_currMacroScope_3847_);
v___x_3903_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3852_);
lean_ctor_set(v___x_3903_, 1, v___x_3900_);
lean_ctor_set(v___x_3903_, 2, v___x_3902_);
lean_ctor_set(v___x_3903_, 3, v___x_3872_);
v___x_3904_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__3___redArg___closed__8));
v___x_3905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3852_);
lean_ctor_set(v___x_3905_, 1, v___x_3904_);
v___x_3906_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__16);
v___x_3907_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___closed__17));
v___x_3908_ = l_Lean_addMacroScope(v_quotContext_3846_, v___x_3907_, v_currMacroScope_3847_);
v___x_3909_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3852_);
lean_ctor_set(v___x_3909_, 1, v___x_3906_);
lean_ctor_set(v___x_3909_, 2, v___x_3908_);
lean_ctor_set(v___x_3909_, 3, v___x_3872_);
v___x_3910_ = l_Lean_Syntax_node3(v___x_3852_, v___x_3899_, v___x_3903_, v___x_3905_, v___x_3909_);
v___x_3911_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkAuxFunction___closed__26));
v___x_3912_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3911_, v___x_3857_, v___x_3857_);
v___x_3913_ = l_Lean_Syntax_node4(v___x_3852_, v___x_3896_, v___x_3898_, v___x_3910_, v___x_3912_, v___x_3857_);
v___x_3914_ = l_Lean_Syntax_node5(v___x_3852_, v___x_3859_, v___x_3861_, v___x_3864_, v___x_3895_, v___x_3913_, v___x_3857_);
v___x_3915_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3853_, v___x_3858_, v___x_3914_);
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg___boxed(lean_object* v_ctx_3917_, lean_object* v_name_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3917_, v_name_3918_, v_a_3919_);
lean_dec_ref(v_a_3919_);
lean_dec_ref(v_ctx_3917_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun(lean_object* v_ctx_3922_, lean_object* v_name_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3922_, v_name_3923_, v_a_3928_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___boxed(lean_object* v_ctx_3932_, lean_object* v_name_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun(v_ctx_3932_, v_name_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3936_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec_ref(v_ctx_3932_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(lean_object* v_ctx_3942_, lean_object* v_name_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v___x_3951_; lean_object* v_a_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; uint8_t v___x_3957_; lean_object* v___x_3958_; 
lean_inc(v_name_3943_);
v___x_3951_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumFun___redArg(v_ctx_3942_, v_name_3943_, v_a_3948_);
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref(v___x_3951_);
v___x_3953_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_3954_ = lean_unsigned_to_nat(1u);
v___x_3955_ = lean_mk_empty_array_with_capacity(v___x_3954_);
lean_inc_ref(v___x_3955_);
v___x_3956_ = lean_array_push(v___x_3955_, v_name_3943_);
v___x_3957_ = 1;
v___x_3958_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_3942_, v___x_3953_, v___x_3956_, v___x_3957_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
lean_dec_ref(v___x_3956_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_toCold_3959_; lean_object* v_options_3960_; lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_4001_; 
v_toCold_3959_ = lean_ctor_get(v_a_3948_, 0);
v_options_3960_ = lean_ctor_get(v_toCold_3959_, 2);
v_a_3961_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3963_ = v___x_3958_;
v_isShared_3964_ = v_isSharedCheck_4001_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3958_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_4001_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v_inheritedTraceOptions_3965_; uint8_t v_hasTrace_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v_inheritedTraceOptions_3965_ = lean_ctor_get(v_toCold_3959_, 11);
v_hasTrace_3966_ = lean_ctor_get_uint8(v_options_3960_, sizeof(void*)*1);
v___x_3967_ = lean_array_push(v___x_3955_, v_a_3952_);
v___x_3968_ = l_Array_append___redArg(v___x_3967_, v_a_3961_);
lean_dec(v_a_3961_);
if (v_hasTrace_3966_ == 0)
{
lean_object* v___x_3970_; 
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v___x_3968_);
v___x_3970_ = v___x_3963_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3968_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
else
{
lean_object* v___x_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; 
v___x_3972_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_3973_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__3);
v___x_3974_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3965_, v_options_3960_, v___x_3973_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3976_; 
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v___x_3968_);
v___x_3976_ = v___x_3963_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3968_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
else
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
lean_del_object(v___x_3963_);
v___x_3978_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__5);
lean_inc_ref(v___x_3968_);
v___x_3979_ = lean_array_to_list(v___x_3968_);
v___x_3980_ = lean_box(0);
v___x_3981_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__0(v___x_3979_, v___x_3980_);
v___x_3982_ = l_Lean_MessageData_ofList(v___x_3981_);
v___x_3983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3978_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds_spec__1___redArg(v___x_3972_, v___x_3983_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_3991_ == 0)
{
lean_object* v_unused_3992_; 
v_unused_3992_ = lean_ctor_get(v___x_3984_, 0);
lean_dec(v_unused_3992_);
v___x_3986_ = v___x_3984_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_dec(v___x_3984_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v___x_3968_);
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3968_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_dec_ref(v___x_3968_);
v_a_3993_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3984_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3984_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v___x_3955_);
lean_dec(v_a_3952_);
v_a_4002_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3958_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3958_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd___boxed(lean_object* v_ctx_4010_, lean_object* v_name_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(v_ctx_4010_, v_name_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(lean_object* v___y_4020_){
_start:
{
lean_object* v___x_4022_; lean_object* v_env_4023_; lean_object* v___x_4024_; lean_object* v_mainModule_4025_; lean_object* v___x_4026_; 
v___x_4022_ = lean_st_ref_get(v___y_4020_);
v_env_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc_ref(v_env_4023_);
lean_dec(v___x_4022_);
v___x_4024_ = l_Lean_Environment_header(v_env_4023_);
lean_dec_ref(v_env_4023_);
v_mainModule_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_mainModule_4025_);
lean_dec_ref(v___x_4024_);
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v_mainModule_4025_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg___boxed(lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_4027_);
lean_dec(v___y_4027_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0(lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_4031_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___boxed(lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0(v___y_4034_, v___y_4035_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0(uint8_t v_a_4038_, lean_object* v_a_4039_, lean_object* v_declName_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
if (v_a_4038_ == 0)
{
lean_object* v___x_4048_; 
v___x_4048_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds(v_a_4039_, v_declName_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4048_;
}
else
{
lean_object* v___x_4049_; 
v___x_4049_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqEnumCmd(v_a_4039_, v_declName_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0___boxed(lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_declName_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
uint8_t v_a_6130__boxed_4060_; lean_object* v_res_4061_; 
v_a_6130__boxed_4060_ = lean_unbox(v_a_4050_);
v_res_4061_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0(v_a_6130__boxed_4060_, v_a_4051_, v_declName_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
return v_res_4061_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4062_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
return v___x_4064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_4066_ = lean_unsigned_to_nat(0u);
v___x_4067_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
lean_ctor_set(v___x_4067_, 2, v___x_4066_);
lean_ctor_set(v___x_4067_, 3, v___x_4066_);
lean_ctor_set(v___x_4067_, 4, v___x_4065_);
lean_ctor_set(v___x_4067_, 5, v___x_4065_);
lean_ctor_set(v___x_4067_, 6, v___x_4065_);
lean_ctor_set(v___x_4067_, 7, v___x_4065_);
lean_ctor_set(v___x_4067_, 8, v___x_4065_);
lean_ctor_set(v___x_4067_, 9, v___x_4065_);
lean_ctor_set(v___x_4067_, 10, v___x_4065_);
return v___x_4067_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4068_ = lean_unsigned_to_nat(32u);
v___x_4069_ = lean_mk_empty_array_with_capacity(v___x_4068_);
v___x_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
return v___x_4070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4071_ = ((size_t)5ULL);
v___x_4072_ = lean_unsigned_to_nat(0u);
v___x_4073_ = lean_unsigned_to_nat(32u);
v___x_4074_ = lean_mk_empty_array_with_capacity(v___x_4073_);
v___x_4075_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_4076_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
lean_ctor_set(v___x_4076_, 1, v___x_4074_);
lean_ctor_set(v___x_4076_, 2, v___x_4072_);
lean_ctor_set(v___x_4076_, 3, v___x_4072_);
lean_ctor_set_usize(v___x_4076_, 4, v___x_4071_);
return v___x_4076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4077_ = lean_box(1);
v___x_4078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_4079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_4080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set(v___x_4080_, 1, v___x_4078_);
lean_ctor_set(v___x_4080_, 2, v___x_4077_);
return v___x_4080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_4083_ = l_Lean_stringToMessageData(v___x_4082_);
return v___x_4083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_4086_ = l_Lean_stringToMessageData(v___x_4085_);
return v___x_4086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_4089_ = l_Lean_stringToMessageData(v___x_4088_);
return v___x_4089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_4092_ = l_Lean_stringToMessageData(v___x_4091_);
return v___x_4092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_4095_ = l_Lean_stringToMessageData(v___x_4094_);
return v___x_4095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_4098_ = l_Lean_stringToMessageData(v___x_4097_);
return v___x_4098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4100_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_4101_ = l_Lean_stringToMessageData(v___x_4100_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_4102_, lean_object* v_declHint_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v___x_4106_; lean_object* v_env_4107_; uint8_t v___x_4108_; 
v___x_4106_ = lean_st_ref_get(v___y_4104_);
v_env_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc_ref(v_env_4107_);
lean_dec(v___x_4106_);
v___x_4108_ = l_Lean_Name_isAnonymous(v_declHint_4103_);
if (v___x_4108_ == 0)
{
uint8_t v_isExporting_4109_; 
v_isExporting_4109_ = lean_ctor_get_uint8(v_env_4107_, sizeof(void*)*8);
if (v_isExporting_4109_ == 0)
{
lean_object* v___x_4110_; 
lean_dec_ref(v_env_4107_);
lean_dec(v_declHint_4103_);
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v_msg_4102_);
return v___x_4110_;
}
else
{
lean_object* v___x_4111_; uint8_t v___x_4112_; 
lean_inc_ref(v_env_4107_);
v___x_4111_ = l_Lean_Environment_setExporting(v_env_4107_, v___x_4108_);
lean_inc(v_declHint_4103_);
lean_inc_ref(v___x_4111_);
v___x_4112_ = l_Lean_Environment_contains(v___x_4111_, v_declHint_4103_, v_isExporting_4109_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; 
lean_dec_ref(v___x_4111_);
lean_dec_ref(v_env_4107_);
lean_dec(v_declHint_4103_);
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_msg_4102_);
return v___x_4113_;
}
else
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v_c_4119_; lean_object* v___x_4120_; 
v___x_4114_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_4115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_4116_ = l_Lean_Options_empty;
v___x_4117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4111_);
lean_ctor_set(v___x_4117_, 1, v___x_4114_);
lean_ctor_set(v___x_4117_, 2, v___x_4115_);
lean_ctor_set(v___x_4117_, 3, v___x_4116_);
lean_inc(v_declHint_4103_);
v___x_4118_ = l_Lean_MessageData_ofConstName(v_declHint_4103_, v___x_4108_);
v_c_4119_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4119_, 0, v___x_4117_);
lean_ctor_set(v_c_4119_, 1, v___x_4118_);
v___x_4120_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4107_, v_declHint_4103_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
lean_dec_ref(v_env_4107_);
lean_dec(v_declHint_4103_);
v___x_4121_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
lean_ctor_set(v___x_4122_, 1, v_c_4119_);
v___x_4123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_4124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4122_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = l_Lean_MessageData_note(v___x_4124_);
v___x_4126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4126_, 0, v_msg_4102_);
lean_ctor_set(v___x_4126_, 1, v___x_4125_);
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
return v___x_4127_;
}
else
{
lean_object* v_val_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4163_; 
v_val_4128_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4130_ = v___x_4120_;
v_isShared_4131_ = v_isSharedCheck_4163_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_val_4128_);
lean_dec(v___x_4120_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4163_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v_mod_4135_; uint8_t v___x_4136_; 
v___x_4132_ = lean_box(0);
v___x_4133_ = l_Lean_Environment_header(v_env_4107_);
lean_dec_ref(v_env_4107_);
v___x_4134_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4133_);
v_mod_4135_ = lean_array_get(v___x_4132_, v___x_4134_, v_val_4128_);
lean_dec(v_val_4128_);
lean_dec_ref(v___x_4134_);
v___x_4136_ = l_Lean_isPrivateName(v_declHint_4103_);
lean_dec(v_declHint_4103_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4148_; 
v___x_4137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_4138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
lean_ctor_set(v___x_4138_, 1, v_c_4119_);
v___x_4139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = l_Lean_MessageData_ofName(v_mod_4135_);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4140_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_4144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4142_);
lean_ctor_set(v___x_4144_, 1, v___x_4143_);
v___x_4145_ = l_Lean_MessageData_note(v___x_4144_);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v_msg_4102_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set_tag(v___x_4130_, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4146_);
v___x_4148_ = v___x_4130_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
else
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4161_; 
v___x_4150_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_4151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
lean_ctor_set(v___x_4151_, 1, v_c_4119_);
v___x_4152_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_4153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4151_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = l_Lean_MessageData_ofName(v_mod_4135_);
v___x_4155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4153_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_4157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4155_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = l_Lean_MessageData_note(v___x_4157_);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v_msg_4102_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set_tag(v___x_4130_, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4159_);
v___x_4161_ = v___x_4130_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4159_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4164_; 
lean_dec_ref(v_env_4107_);
lean_dec(v_declHint_4103_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v_msg_4102_);
return v___x_4164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_4165_, lean_object* v_declHint_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4165_, v_declHint_4166_, v___y_4167_);
lean_dec(v___y_4167_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_4170_, lean_object* v_declHint_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v___x_4175_; lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4185_; 
v___x_4175_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4170_, v_declHint_4171_, v___y_4173_);
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4178_ = v___x_4175_;
v_isShared_4179_ = v_isSharedCheck_4185_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4185_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4180_ = l_Lean_unknownIdentifierMessageTag;
v___x_4181_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
lean_ctor_set(v___x_4181_, 1, v_a_4176_);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 0, v___x_4181_);
v___x_4183_ = v___x_4178_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_4186_, lean_object* v_declHint_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_4186_, v_declHint_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(lean_object* v_msgData_4192_, lean_object* v_macroStack_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v___x_4196_; lean_object* v_scopes_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v_opts_4200_; lean_object* v___x_4201_; uint8_t v___x_4202_; 
v___x_4196_ = lean_st_ref_get(v___y_4194_);
v_scopes_4197_ = lean_ctor_get(v___x_4196_, 2);
lean_inc(v_scopes_4197_);
lean_dec(v___x_4196_);
v___x_4198_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4199_ = l_List_head_x21___redArg(v___x_4198_, v_scopes_4197_);
lean_dec(v_scopes_4197_);
v_opts_4200_ = lean_ctor_get(v___x_4199_, 1);
lean_inc_ref(v_opts_4200_);
lean_dec(v___x_4199_);
v___x_4201_ = l_Lean_Elab_pp_macroStack;
v___x_4202_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__10(v_opts_4200_, v___x_4201_);
lean_dec_ref(v_opts_4200_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4203_; 
lean_dec(v_macroStack_4193_);
v___x_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4203_, 0, v_msgData_4192_);
return v___x_4203_;
}
else
{
if (lean_obj_tag(v_macroStack_4193_) == 0)
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v_msgData_4192_);
return v___x_4204_;
}
else
{
lean_object* v_head_4205_; lean_object* v_after_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4221_; 
v_head_4205_ = lean_ctor_get(v_macroStack_4193_, 0);
lean_inc(v_head_4205_);
v_after_4206_ = lean_ctor_get(v_head_4205_, 1);
v_isSharedCheck_4221_ = !lean_is_exclusive(v_head_4205_);
if (v_isSharedCheck_4221_ == 0)
{
lean_object* v_unused_4222_; 
v_unused_4222_ = lean_ctor_get(v_head_4205_, 0);
lean_dec(v_unused_4222_);
v___x_4208_ = v_head_4205_;
v_isShared_4209_ = v_isSharedCheck_4221_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_after_4206_);
lean_dec(v_head_4205_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4221_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4210_; lean_object* v___x_4212_; 
v___x_4210_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_4209_ == 0)
{
lean_ctor_set_tag(v___x_4208_, 7);
lean_ctor_set(v___x_4208_, 1, v___x_4210_);
lean_ctor_set(v___x_4208_, 0, v_msgData_4192_);
v___x_4212_ = v___x_4208_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_msgData_4192_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v_msgData_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4213_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_4214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4212_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
v___x_4215_ = l_Lean_MessageData_ofSyntax(v_after_4206_);
v___x_4216_ = l_Lean_indentD(v___x_4215_);
v_msgData_4217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4217_, 0, v___x_4214_);
lean_ctor_set(v_msgData_4217_, 1, v___x_4216_);
v___x_4218_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_msgData_4217_, v_macroStack_4193_);
v___x_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4218_);
return v___x_4219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_msgData_4223_, lean_object* v_macroStack_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_msgData_4223_, v_macroStack_4224_, v___y_4225_);
lean_dec(v___y_4225_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(lean_object* v_msgData_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v___x_4231_; lean_object* v_env_4232_; lean_object* v___x_4233_; lean_object* v_scopes_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v_opts_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4231_ = lean_st_ref_get(v___y_4229_);
v_env_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc_ref(v_env_4232_);
lean_dec(v___x_4231_);
v___x_4233_ = lean_st_ref_get(v___y_4229_);
v_scopes_4234_ = lean_ctor_get(v___x_4233_, 2);
lean_inc(v_scopes_4234_);
lean_dec(v___x_4233_);
v___x_4235_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4236_ = l_List_head_x21___redArg(v___x_4235_, v_scopes_4234_);
lean_dec(v_scopes_4234_);
v_opts_4237_ = lean_ctor_get(v___x_4236_, 1);
lean_inc_ref(v_opts_4237_);
lean_dec(v___x_4236_);
v___x_4238_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_4239_ = lean_unsigned_to_nat(32u);
v___x_4240_ = lean_mk_empty_array_with_capacity(v___x_4239_);
lean_dec_ref(v___x_4240_);
v___x_4241_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_4242_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4242_, 0, v_env_4232_);
lean_ctor_set(v___x_4242_, 1, v___x_4238_);
lean_ctor_set(v___x_4242_, 2, v___x_4241_);
lean_ctor_set(v___x_4242_, 3, v_opts_4237_);
v___x_4243_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4242_);
lean_ctor_set(v___x_4243_, 1, v_msgData_4228_);
v___x_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msgData_4245_, v___y_4246_);
lean_dec(v___y_4246_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_Elab_Command_getRef___redArg(v___y_4250_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v_macroStack_4255_; lean_object* v___x_4256_; lean_object* v_a_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4268_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
v_macroStack_4255_ = lean_ctor_get(v___y_4250_, 4);
v___x_4256_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msg_4249_, v___y_4251_);
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref(v___x_4256_);
v___x_4258_ = l_Lean_Elab_getBetterRef(v_a_4254_, v_macroStack_4255_);
lean_dec(v_a_4254_);
lean_inc(v_macroStack_4255_);
v___x_4259_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_a_4257_, v_macroStack_4255_, v___y_4251_);
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4262_ = v___x_4259_;
v_isShared_4263_ = v_isSharedCheck_4268_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4259_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4268_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4264_; lean_object* v___x_4266_; 
v___x_4264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4258_);
lean_ctor_set(v___x_4264_, 1, v_a_4260_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set_tag(v___x_4262_, 1);
lean_ctor_set(v___x_4262_, 0, v___x_4264_);
v___x_4266_ = v___x_4262_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4264_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec_ref(v_msg_4249_);
v_a_4269_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4253_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4253_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4277_, v___y_4278_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_4282_, lean_object* v_msg_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lean_Elab_Command_getRef___redArg(v___y_4284_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v_fileName_4289_; lean_object* v_fileMap_4290_; lean_object* v_currRecDepth_4291_; lean_object* v_cmdPos_4292_; lean_object* v_macroStack_4293_; lean_object* v_quotContext_x3f_4294_; lean_object* v_currMacroScope_4295_; lean_object* v_snap_x3f_4296_; lean_object* v_cancelTk_x3f_4297_; uint8_t v_suppressElabErrors_4298_; lean_object* v_ref_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___x_4287_, 1);
v_fileName_4289_ = lean_ctor_get(v___y_4284_, 0);
v_fileMap_4290_ = lean_ctor_get(v___y_4284_, 1);
v_currRecDepth_4291_ = lean_ctor_get(v___y_4284_, 2);
v_cmdPos_4292_ = lean_ctor_get(v___y_4284_, 3);
v_macroStack_4293_ = lean_ctor_get(v___y_4284_, 4);
v_quotContext_x3f_4294_ = lean_ctor_get(v___y_4284_, 5);
v_currMacroScope_4295_ = lean_ctor_get(v___y_4284_, 6);
v_snap_x3f_4296_ = lean_ctor_get(v___y_4284_, 8);
v_cancelTk_x3f_4297_ = lean_ctor_get(v___y_4284_, 9);
v_suppressElabErrors_4298_ = lean_ctor_get_uint8(v___y_4284_, sizeof(void*)*10);
v_ref_4299_ = l_Lean_replaceRef(v_ref_4282_, v_a_4288_);
lean_dec(v_a_4288_);
lean_inc(v_cancelTk_x3f_4297_);
lean_inc(v_snap_x3f_4296_);
lean_inc(v_currMacroScope_4295_);
lean_inc(v_quotContext_x3f_4294_);
lean_inc(v_macroStack_4293_);
lean_inc(v_cmdPos_4292_);
lean_inc(v_currRecDepth_4291_);
lean_inc_ref(v_fileMap_4290_);
lean_inc_ref(v_fileName_4289_);
v___x_4300_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4300_, 0, v_fileName_4289_);
lean_ctor_set(v___x_4300_, 1, v_fileMap_4290_);
lean_ctor_set(v___x_4300_, 2, v_currRecDepth_4291_);
lean_ctor_set(v___x_4300_, 3, v_cmdPos_4292_);
lean_ctor_set(v___x_4300_, 4, v_macroStack_4293_);
lean_ctor_set(v___x_4300_, 5, v_quotContext_x3f_4294_);
lean_ctor_set(v___x_4300_, 6, v_currMacroScope_4295_);
lean_ctor_set(v___x_4300_, 7, v_ref_4299_);
lean_ctor_set(v___x_4300_, 8, v_snap_x3f_4296_);
lean_ctor_set(v___x_4300_, 9, v_cancelTk_x3f_4297_);
lean_ctor_set_uint8(v___x_4300_, sizeof(void*)*10, v_suppressElabErrors_4298_);
v___x_4301_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4283_, v___x_4300_, v___y_4285_);
lean_dec_ref_known(v___x_4300_, 10);
return v___x_4301_;
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_dec_ref(v_msg_4283_);
v_a_4302_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4287_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4287_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_4310_, lean_object* v_msg_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4310_, v_msg_4311_, v___y_4312_, v___y_4313_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec(v_ref_4310_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_4316_, lean_object* v_msg_4317_, lean_object* v_declHint_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v___x_4322_; lean_object* v_a_4323_; lean_object* v___x_4324_; 
v___x_4322_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_4317_, v_declHint_4318_, v___y_4319_, v___y_4320_);
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
lean_dec_ref(v___x_4322_);
v___x_4324_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4316_, v_a_4323_, v___y_4319_, v___y_4320_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_4325_, lean_object* v_msg_4326_, lean_object* v_declHint_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4325_, v_msg_4326_, v_declHint_4327_, v___y_4328_, v___y_4329_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec(v_ref_4325_);
return v_res_4331_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__0));
v___x_4334_ = l_Lean_stringToMessageData(v___x_4333_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_4335_, lean_object* v_constName_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v___x_4340_; uint8_t v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4340_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_4341_ = 0;
lean_inc(v_constName_4336_);
v___x_4342_ = l_Lean_MessageData_ofConstName(v_constName_4336_, v___x_4341_);
v___x_4343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4340_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
v___x_4344_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_4345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4343_);
lean_ctor_set(v___x_4345_, 1, v___x_4344_);
v___x_4346_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4335_, v___x_4345_, v_constName_4336_, v___y_4337_, v___y_4338_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_4347_, lean_object* v_constName_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_4347_, v_constName_4348_, v___y_4349_, v___y_4350_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v_ref_4347_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(lean_object* v_constName_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l_Lean_Elab_Command_getRef___redArg(v___y_4354_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v___x_4359_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
v___x_4359_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_a_4358_, v_constName_4353_, v___y_4354_, v___y_4355_);
lean_dec(v_a_4358_);
return v___x_4359_;
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec(v_constName_4353_);
v_a_4360_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4357_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4357_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_constName_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4368_, v___y_4369_, v___y_4370_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(lean_object* v_constName_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v___x_4377_; lean_object* v_env_4378_; uint8_t v___x_4379_; lean_object* v___x_4380_; 
v___x_4377_ = lean_st_ref_get(v___y_4375_);
v_env_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc_ref(v_env_4378_);
lean_dec(v___x_4377_);
v___x_4379_ = 0;
lean_inc(v_constName_4373_);
v___x_4380_ = l_Lean_Environment_find_x3f(v_env_4378_, v_constName_4373_, v___x_4379_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v___x_4381_; 
v___x_4381_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4373_, v___y_4374_, v___y_4375_);
return v___x_4381_;
}
else
{
lean_object* v_val_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
lean_dec(v_constName_4373_);
v_val_4382_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4380_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_val_4382_);
lean_dec(v___x_4380_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
lean_ctor_set_tag(v___x_4384_, 0);
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_val_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1___boxed(lean_object* v_constName_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_constName_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(uint8_t v___x_4395_, lean_object* v_x_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
if (lean_obj_tag(v_x_4396_) == 0)
{
uint8_t v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4400_ = 1;
v___x_4401_ = lean_box(v___x_4400_);
v___x_4402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4401_);
return v___x_4402_;
}
else
{
lean_object* v_head_4403_; lean_object* v_tail_4404_; lean_object* v___x_4405_; 
v_head_4403_ = lean_ctor_get(v_x_4396_, 0);
lean_inc(v_head_4403_);
v_tail_4404_ = lean_ctor_get(v_x_4396_, 1);
lean_inc(v_tail_4404_);
lean_dec_ref_known(v_x_4396_, 2);
v___x_4405_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_head_4403_, v___y_4397_, v___y_4398_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4426_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4408_ = v___x_4405_;
v_isShared_4409_ = v_isSharedCheck_4426_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4405_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4426_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___y_4411_; uint8_t v_a_4412_; 
if (lean_obj_tag(v_a_4406_) == 6)
{
lean_object* v_val_4414_; lean_object* v_numFields_4415_; lean_object* v___x_4416_; uint8_t v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4420_; 
v_val_4414_ = lean_ctor_get(v_a_4406_, 0);
lean_inc_ref(v_val_4414_);
lean_dec_ref_known(v_a_4406_, 1);
v_numFields_4415_ = lean_ctor_get(v_val_4414_, 4);
lean_inc(v_numFields_4415_);
lean_dec_ref(v_val_4414_);
v___x_4416_ = lean_unsigned_to_nat(0u);
v___x_4417_ = lean_nat_dec_eq(v_numFields_4415_, v___x_4416_);
lean_dec(v_numFields_4415_);
v___x_4418_ = lean_box(v___x_4417_);
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 0, v___x_4418_);
v___x_4420_ = v___x_4408_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4418_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
v___y_4411_ = v___x_4420_;
v_a_4412_ = v___x_4417_;
goto v___jp_4410_;
}
}
else
{
lean_object* v___x_4422_; lean_object* v___x_4424_; 
lean_dec(v_a_4406_);
v___x_4422_ = lean_box(v___x_4395_);
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 0, v___x_4422_);
v___x_4424_ = v___x_4408_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
v___y_4411_ = v___x_4424_;
v_a_4412_ = v___x_4395_;
goto v___jp_4410_;
}
}
v___jp_4410_:
{
if (v_a_4412_ == 0)
{
lean_dec(v_tail_4404_);
return v___y_4411_;
}
else
{
lean_dec_ref(v___y_4411_);
v_x_4396_ = v_tail_4404_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec(v_tail_4404_);
v_a_4427_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4405_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4405_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2___boxed(lean_object* v___x_4435_, lean_object* v_x_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
uint8_t v___x_6783__boxed_4440_; lean_object* v_res_4441_; 
v___x_6783__boxed_4440_ = lean_unbox(v___x_4435_);
v_res_4441_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(v___x_6783__boxed_4440_, v_x_4436_, v___y_4437_, v___y_4438_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(lean_object* v_declName_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v___x_4446_; 
v___x_4446_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1(v_declName_4442_, v___y_4443_, v___y_4444_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4502_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4502_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4446_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4502_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
if (lean_obj_tag(v_a_4447_) == 5)
{
lean_object* v_val_4451_; lean_object* v_toConstantVal_4452_; lean_object* v_numParams_4453_; lean_object* v_numIndices_4454_; lean_object* v_ctors_4455_; uint8_t v_isRec_4456_; uint8_t v_isUnsafe_4457_; lean_object* v_type_4458_; uint8_t v___x_4459_; 
v_val_4451_ = lean_ctor_get(v_a_4447_, 0);
lean_inc_ref(v_val_4451_);
lean_dec_ref_known(v_a_4447_, 1);
v_toConstantVal_4452_ = lean_ctor_get(v_val_4451_, 0);
v_numParams_4453_ = lean_ctor_get(v_val_4451_, 1);
lean_inc(v_numParams_4453_);
v_numIndices_4454_ = lean_ctor_get(v_val_4451_, 2);
lean_inc(v_numIndices_4454_);
v_ctors_4455_ = lean_ctor_get(v_val_4451_, 4);
lean_inc(v_ctors_4455_);
v_isRec_4456_ = lean_ctor_get_uint8(v_val_4451_, sizeof(void*)*6);
v_isUnsafe_4457_ = lean_ctor_get_uint8(v_val_4451_, sizeof(void*)*6 + 1);
v_type_4458_ = lean_ctor_get(v_toConstantVal_4452_, 2);
v___x_4459_ = l_Lean_Expr_isProp(v_type_4458_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4460_; lean_object* v___x_4461_; uint8_t v___x_4462_; 
v___x_4460_ = l_Lean_InductiveVal_numTypeFormers(v_val_4451_);
lean_dec_ref(v_val_4451_);
v___x_4461_ = lean_unsigned_to_nat(1u);
v___x_4462_ = lean_nat_dec_eq(v___x_4460_, v___x_4461_);
lean_dec(v___x_4460_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; lean_object* v___x_4465_; 
lean_dec(v_ctors_4455_);
lean_dec(v_numIndices_4454_);
lean_dec(v_numParams_4453_);
v___x_4463_ = lean_box(v___x_4462_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4463_);
v___x_4465_ = v___x_4449_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
else
{
lean_object* v___x_4467_; uint8_t v___x_4468_; 
v___x_4467_ = lean_unsigned_to_nat(0u);
v___x_4468_ = lean_nat_dec_eq(v_numIndices_4454_, v___x_4467_);
lean_dec(v_numIndices_4454_);
if (v___x_4468_ == 0)
{
lean_object* v___x_4469_; lean_object* v___x_4471_; 
lean_dec(v_ctors_4455_);
lean_dec(v_numParams_4453_);
v___x_4469_ = lean_box(v___x_4468_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4469_);
v___x_4471_ = v___x_4449_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4469_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
else
{
uint8_t v___x_4473_; 
v___x_4473_ = lean_nat_dec_eq(v_numParams_4453_, v___x_4467_);
lean_dec(v_numParams_4453_);
if (v___x_4473_ == 0)
{
lean_object* v___x_4474_; lean_object* v___x_4476_; 
lean_dec(v_ctors_4455_);
v___x_4474_ = lean_box(v___x_4473_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4474_);
v___x_4476_ = v___x_4449_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4474_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
else
{
uint8_t v___x_4478_; 
v___x_4478_ = l_List_isEmpty___redArg(v_ctors_4455_);
if (v___x_4478_ == 0)
{
if (v_isRec_4456_ == 0)
{
if (v_isUnsafe_4457_ == 0)
{
lean_object* v___x_4479_; 
lean_del_object(v___x_4449_);
v___x_4479_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__2(v_isUnsafe_4457_, v_ctors_4455_, v___y_4443_, v___y_4444_);
return v___x_4479_;
}
else
{
lean_object* v___x_4480_; lean_object* v___x_4482_; 
lean_dec(v_ctors_4455_);
v___x_4480_ = lean_box(v_isRec_4456_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4480_);
v___x_4482_ = v___x_4449_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
else
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
lean_dec(v_ctors_4455_);
v___x_4484_ = lean_box(v___x_4478_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4484_);
v___x_4486_ = v___x_4449_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4484_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
else
{
lean_object* v___x_4488_; lean_object* v___x_4490_; 
lean_dec(v_ctors_4455_);
v___x_4488_ = lean_box(v___x_4459_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4488_);
v___x_4490_ = v___x_4449_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4488_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
}
}
else
{
uint8_t v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4495_; 
lean_dec(v_ctors_4455_);
lean_dec(v_numIndices_4454_);
lean_dec(v_numParams_4453_);
lean_dec_ref(v_val_4451_);
v___x_4492_ = 0;
v___x_4493_ = lean_box(v___x_4492_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4493_);
v___x_4495_ = v___x_4449_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
else
{
uint8_t v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4500_; 
lean_dec(v_a_4447_);
v___x_4497_ = 0;
v___x_4498_ = lean_box(v___x_4497_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4498_);
v___x_4500_ = v___x_4449_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4498_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
else
{
lean_object* v_a_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4510_; 
v_a_4503_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4505_ = v___x_4446_;
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_a_4503_);
lean_dec(v___x_4446_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4508_; 
if (v_isShared_4506_ == 0)
{
v___x_4508_ = v___x_4505_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4503_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1___boxed(lean_object* v_declName_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(v_declName_4511_, v___y_4512_, v___y_4513_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(lean_object* v_as_4516_, size_t v_i_4517_, size_t v_stop_4518_, lean_object* v_b_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
uint8_t v___x_4523_; 
v___x_4523_ = lean_usize_dec_eq(v_i_4517_, v_stop_4518_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4524_ = lean_array_uget_borrowed(v_as_4516_, v_i_4517_);
lean_inc(v___x_4524_);
v___x_4525_ = l_Lean_Elab_Command_elabCommand(v___x_4524_, v___y_4520_, v___y_4521_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_object* v_a_4526_; size_t v___x_4527_; size_t v___x_4528_; 
v_a_4526_ = lean_ctor_get(v___x_4525_, 0);
lean_inc(v_a_4526_);
lean_dec_ref_known(v___x_4525_, 1);
v___x_4527_ = ((size_t)1ULL);
v___x_4528_ = lean_usize_add(v_i_4517_, v___x_4527_);
v_i_4517_ = v___x_4528_;
v_b_4519_ = v_a_4526_;
goto _start;
}
else
{
return v___x_4525_;
}
}
else
{
lean_object* v___x_4530_; 
v___x_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4530_, 0, v_b_4519_);
return v___x_4530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2___boxed(lean_object* v_as_4531_, lean_object* v_i_4532_, lean_object* v_stop_4533_, lean_object* v_b_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
size_t v_i_boxed_4538_; size_t v_stop_boxed_4539_; lean_object* v_res_4540_; 
v_i_boxed_4538_ = lean_unbox_usize(v_i_4532_);
lean_dec(v_i_4532_);
v_stop_boxed_4539_ = lean_unbox_usize(v_stop_4533_);
lean_dec(v_stop_4533_);
v_res_4540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_as_4531_, v_i_boxed_4538_, v_stop_boxed_4539_, v_b_4534_, v___y_4535_, v___y_4536_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
lean_dec_ref(v_as_4531_);
return v_res_4540_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11(void){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__10));
v___x_4569_ = l_String_toRawSubstring_x27(v___x_4568_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1(lean_object* v___x_4573_, lean_object* v_declName_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v_a_4582_; lean_object* v___x_4609_; 
v___x_4609_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4573_, v___y_4575_, v___y_4576_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4680_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4612_ = v___x_4609_;
v_isShared_4613_ = v_isSharedCheck_4680_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4609_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4680_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___y_4647_; lean_object* v___x_4648_; 
lean_inc(v_declName_4574_);
v___x_4648_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1(v_declName_4574_, v___y_4575_, v___y_4576_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v_a_4649_; lean_object* v___y_4650_; lean_object* v___x_4651_; 
v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
lean_inc(v_a_4649_);
lean_dec_ref_known(v___x_4648_, 1);
lean_inc(v_a_4610_);
v___y_4650_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__0___boxed), 10, 3);
lean_closure_set(v___y_4650_, 0, v_a_4649_);
lean_closure_set(v___y_4650_, 1, v_a_4610_);
lean_closure_set(v___y_4650_, 2, v_declName_4574_);
v___x_4651_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_4650_, v___y_4575_, v___y_4576_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v_a_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; uint8_t v___x_4655_; 
v_a_4652_ = lean_ctor_get(v___x_4651_, 0);
lean_inc(v_a_4652_);
lean_dec_ref_known(v___x_4651_, 1);
v___x_4653_ = lean_unsigned_to_nat(0u);
v___x_4654_ = lean_array_get_size(v_a_4652_);
v___x_4655_ = lean_nat_dec_lt(v___x_4653_, v___x_4654_);
if (v___x_4655_ == 0)
{
lean_dec(v_a_4652_);
goto v___jp_4614_;
}
else
{
lean_object* v___x_4656_; uint8_t v___x_4657_; 
v___x_4656_ = lean_box(0);
v___x_4657_ = lean_nat_dec_le(v___x_4654_, v___x_4654_);
if (v___x_4657_ == 0)
{
if (v___x_4655_ == 0)
{
lean_dec(v_a_4652_);
goto v___jp_4614_;
}
else
{
size_t v___x_4658_; size_t v___x_4659_; lean_object* v___x_4660_; 
v___x_4658_ = ((size_t)0ULL);
v___x_4659_ = lean_usize_of_nat(v___x_4654_);
v___x_4660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_a_4652_, v___x_4658_, v___x_4659_, v___x_4656_, v___y_4575_, v___y_4576_);
lean_dec(v_a_4652_);
v___y_4647_ = v___x_4660_;
goto v___jp_4646_;
}
}
else
{
size_t v___x_4661_; size_t v___x_4662_; lean_object* v___x_4663_; 
v___x_4661_ = ((size_t)0ULL);
v___x_4662_ = lean_usize_of_nat(v___x_4654_);
v___x_4663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__2(v_a_4652_, v___x_4661_, v___x_4662_, v___x_4656_, v___y_4575_, v___y_4576_);
lean_dec(v_a_4652_);
v___y_4647_ = v___x_4663_;
goto v___jp_4646_;
}
}
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
lean_del_object(v___x_4612_);
lean_dec(v_a_4610_);
lean_dec_ref(v___y_4575_);
v_a_4664_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4651_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4651_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_del_object(v___x_4612_);
lean_dec(v_a_4610_);
lean_dec_ref(v___y_4575_);
lean_dec(v_declName_4574_);
v_a_4672_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4648_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4648_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
v___jp_4614_:
{
uint8_t v_usePartial_4615_; 
v_usePartial_4615_ = lean_ctor_get_uint8(v_a_4610_, sizeof(void*)*3);
if (v_usePartial_4615_ == 0)
{
lean_object* v_instName_4616_; lean_object* v___x_4617_; 
lean_del_object(v___x_4612_);
v_instName_4616_ = lean_ctor_get(v_a_4610_, 0);
lean_inc(v_instName_4616_);
lean_dec(v_a_4610_);
v___x_4617_ = l_Lean_Elab_Command_getRef___redArg(v___y_4575_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v_a_4618_; lean_object* v___x_4619_; 
v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
lean_inc(v_a_4618_);
lean_dec_ref_known(v___x_4617_, 1);
v___x_4619_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_4575_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_a_4620_; lean_object* v_quotContext_x3f_4621_; lean_object* v___x_4622_; 
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4620_);
lean_dec_ref_known(v___x_4619_, 1);
v_quotContext_x3f_4621_ = lean_ctor_get(v___y_4575_, 5);
v___x_4622_ = l_Lean_SourceInfo_fromRef(v_a_4618_, v_usePartial_4615_);
lean_dec(v_a_4618_);
if (lean_obj_tag(v_quotContext_x3f_4621_) == 0)
{
lean_object* v___x_4623_; lean_object* v_a_4624_; 
v___x_4623_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__0___redArg(v___y_4576_);
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
lean_inc(v_a_4624_);
lean_dec_ref(v___x_4623_);
v___y_4579_ = v_instName_4616_;
v___y_4580_ = v___x_4622_;
v___y_4581_ = v_a_4620_;
v_a_4582_ = v_a_4624_;
goto v___jp_4578_;
}
else
{
lean_object* v_val_4625_; 
v_val_4625_ = lean_ctor_get(v_quotContext_x3f_4621_, 0);
lean_inc(v_val_4625_);
v___y_4579_ = v_instName_4616_;
v___y_4580_ = v___x_4622_;
v___y_4581_ = v_a_4620_;
v_a_4582_ = v_val_4625_;
goto v___jp_4578_;
}
}
else
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4633_; 
lean_dec(v_a_4618_);
lean_dec(v_instName_4616_);
lean_dec_ref(v___y_4575_);
v_a_4626_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4628_ = v___x_4619_;
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4619_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4631_; 
if (v_isShared_4629_ == 0)
{
v___x_4631_ = v___x_4628_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4626_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
}
else
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4641_; 
lean_dec(v_instName_4616_);
lean_dec_ref(v___y_4575_);
v_a_4634_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4636_ = v___x_4617_;
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4617_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4639_; 
if (v_isShared_4637_ == 0)
{
v___x_4639_ = v___x_4636_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4634_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
}
else
{
lean_object* v___x_4642_; lean_object* v___x_4644_; 
lean_dec(v_a_4610_);
lean_dec_ref(v___y_4575_);
v___x_4642_ = lean_box(0);
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v___x_4642_);
v___x_4644_ = v___x_4612_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v___x_4642_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
v___jp_4646_:
{
if (lean_obj_tag(v___y_4647_) == 0)
{
lean_dec_ref_known(v___y_4647_, 1);
goto v___jp_4614_;
}
else
{
lean_del_object(v___x_4612_);
lean_dec(v_a_4610_);
lean_dec_ref(v___y_4575_);
return v___y_4647_;
}
}
}
}
else
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
lean_dec_ref(v___y_4575_);
lean_dec(v_declName_4574_);
v_a_4681_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4683_ = v___x_4609_;
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4609_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
v___jp_4578_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4583_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__0));
v___x_4584_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__1));
lean_inc_n(v___y_4580_, 10);
v___x_4585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4585_, 0, v___y_4580_);
lean_ctor_set(v___x_4585_, 1, v___x_4583_);
v___x_4586_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__2));
v___x_4587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4587_, 0, v___y_4580_);
lean_ctor_set(v___x_4587_, 1, v___x_4586_);
v___x_4588_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__12));
v___x_4589_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__4));
v___x_4590_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__6));
v___x_4591_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkMatchOld_mkElseAlt___closed__13);
v___x_4592_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4592_, 0, v___y_4580_);
lean_ctor_set(v___x_4592_, 1, v___x_4588_);
lean_ctor_set(v___x_4592_, 2, v___x_4591_);
lean_inc_ref(v___x_4592_);
v___x_4593_ = l_Lean_Syntax_node1(v___y_4580_, v___x_4590_, v___x_4592_);
v___x_4594_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__9));
v___x_4595_ = lean_obj_once(&l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11, &l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11_once, _init_l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__11);
v___x_4596_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__12));
v___x_4597_ = l_Lean_addMacroScope(v_a_4582_, v___x_4596_, v___y_4581_);
v___x_4598_ = lean_box(0);
v___x_4599_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4599_, 0, v___y_4580_);
lean_ctor_set(v___x_4599_, 1, v___x_4595_);
lean_ctor_set(v___x_4599_, 2, v___x_4597_);
lean_ctor_set(v___x_4599_, 3, v___x_4598_);
v___x_4600_ = l_Lean_Syntax_node2(v___y_4580_, v___x_4594_, v___x_4599_, v___x_4592_);
v___x_4601_ = l_Lean_Syntax_node2(v___y_4580_, v___x_4589_, v___x_4593_, v___x_4600_);
v___x_4602_ = l_Lean_Syntax_node1(v___y_4580_, v___x_4588_, v___x_4601_);
v___x_4603_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___closed__13));
v___x_4604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4604_, 0, v___y_4580_);
lean_ctor_set(v___x_4604_, 1, v___x_4603_);
v___x_4605_ = l_Lean_mkIdent(v___y_4579_);
v___x_4606_ = l_Lean_Syntax_node1(v___y_4580_, v___x_4588_, v___x_4605_);
v___x_4607_ = l_Lean_Syntax_node5(v___y_4580_, v___x_4584_, v___x_4585_, v___x_4587_, v___x_4602_, v___x_4604_, v___x_4606_);
v___x_4608_ = l_Lean_Elab_Command_elabCommand(v___x_4607_, v___y_4575_, v___y_4576_);
lean_dec_ref(v___y_4575_);
return v___x_4608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___boxed(lean_object* v___x_4689_, lean_object* v_declName_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_){
_start:
{
lean_object* v_res_4694_; 
v_res_4694_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1(v___x_4689_, v_declName_4690_, v___y_4691_, v___y_4692_);
lean_dec(v___y_4692_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(lean_object* v_declName_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_){
_start:
{
lean_object* v___x_4699_; lean_object* v___x_4700_; uint8_t v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___f_4704_; lean_object* v___x_4705_; 
v___x_4699_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_4700_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_));
v___x_4701_ = 1;
v___x_4702_ = lean_box(v___x_4701_);
lean_inc_n(v_declName_4695_, 2);
v___x_4703_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_mkContext___boxed), 11, 4);
lean_closure_set(v___x_4703_, 0, v___x_4699_);
lean_closure_set(v___x_4703_, 1, v___x_4700_);
lean_closure_set(v___x_4703_, 2, v_declName_4695_);
lean_closure_set(v___x_4703_, 3, v___x_4702_);
v___f_4704_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___lam__1___boxed), 5, 2);
lean_closure_set(v___f_4704_, 0, v___x_4703_);
lean_closure_set(v___f_4704_, 1, v_declName_4695_);
v___x_4705_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_4695_, v___f_4704_, v_a_4696_, v_a_4697_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance___boxed(lean_object* v_declName_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(v_declName_4706_, v_a_4707_, v_a_4708_);
lean_dec(v_a_4708_);
lean_dec_ref(v_a_4707_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_4711_, lean_object* v_constName_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_){
_start:
{
lean_object* v___x_4716_; 
v___x_4716_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___redArg(v_constName_4712_, v___y_4713_, v___y_4714_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4717_, lean_object* v_constName_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2(v_00_u03b1_4717_, v_constName_4718_, v___y_4719_, v___y_4720_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_4723_, lean_object* v_ref_4724_, lean_object* v_constName_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v___x_4729_; 
v___x_4729_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_4724_, v_constName_4725_, v___y_4726_, v___y_4727_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4730_, lean_object* v_ref_4731_, lean_object* v_constName_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_4730_, v_ref_4731_, v_constName_4732_, v___y_4733_, v___y_4734_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v_ref_4731_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4737_, lean_object* v_ref_4738_, lean_object* v_msg_4739_, lean_object* v_declHint_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
lean_object* v___x_4744_; 
v___x_4744_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_4738_, v_msg_4739_, v_declHint_4740_, v___y_4741_, v___y_4742_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4745_, lean_object* v_ref_4746_, lean_object* v_msg_4747_, lean_object* v_declHint_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_4745_, v_ref_4746_, v_msg_4747_, v_declHint_4748_, v___y_4749_, v___y_4750_);
lean_dec(v___y_4750_);
lean_dec_ref(v___y_4749_);
lean_dec(v_ref_4746_);
return v_res_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_4753_, lean_object* v_declHint_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_){
_start:
{
lean_object* v___x_4758_; 
v___x_4758_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4753_, v_declHint_4754_, v___y_4756_);
return v___x_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_4759_, lean_object* v_declHint_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
lean_object* v_res_4764_; 
v_res_4764_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7_spec__8(v_msg_4759_, v_declHint_4760_, v___y_4761_, v___y_4762_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_4765_, lean_object* v_ref_4766_, lean_object* v_msg_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
lean_object* v___x_4771_; 
v___x_4771_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_4766_, v_msg_4767_, v___y_4768_, v___y_4769_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_4772_, lean_object* v_ref_4773_, lean_object* v_msg_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_4772_, v_ref_4773_, v_msg_4774_, v___y_4775_, v___y_4776_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v_ref_4773_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v___x_4783_; 
v___x_4783_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___redArg(v_msgData_4779_, v___y_4781_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_4784_, v___y_4785_, v___y_4786_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
return v_res_4788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_4789_, lean_object* v_msg_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4790_, v___y_4791_, v___y_4792_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4795_, lean_object* v_msg_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v_res_4800_; 
v_res_4800_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_4795_, v_msg_4796_, v___y_4797_, v___y_4798_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
return v_res_4800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12(lean_object* v_msgData_4801_, lean_object* v_macroStack_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___redArg(v_msgData_4801_, v_macroStack_4802_, v___y_4804_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12___boxed(lean_object* v_msgData_4807_, lean_object* v_macroStack_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance_spec__1_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10_spec__12(v_msgData_4807_, v_macroStack_4808_, v___y_4809_, v___y_4810_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(lean_object* v_declName_4813_, lean_object* v___y_4814_){
_start:
{
lean_object* v___x_4816_; lean_object* v_env_4817_; uint8_t v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v___x_4816_ = lean_st_ref_get(v___y_4814_);
v_env_4817_ = lean_ctor_get(v___x_4816_, 0);
lean_inc_ref(v_env_4817_);
lean_dec(v___x_4816_);
v___x_4818_ = l_Lean_isInductiveCore(v_env_4817_, v_declName_4813_);
v___x_4819_ = lean_box(v___x_4818_);
v___x_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4819_);
return v___x_4820_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_){
_start:
{
lean_object* v_res_4824_; 
v_res_4824_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v_declName_4821_, v___y_4822_);
lean_dec(v___y_4822_);
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1(lean_object* v_declName_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v_declName_4825_, v___y_4827_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___boxed(lean_object* v_declName_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1(v_declName_4830_, v___y_4831_, v___y_4832_);
lean_dec(v___y_4832_);
lean_dec_ref(v___y_4831_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(uint8_t v_____do__lift_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_){
_start:
{
if (v_____do__lift_4835_ == 0)
{
uint8_t v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4839_ = 1;
v___x_4840_ = lean_box(v___x_4839_);
v___x_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4840_);
return v___x_4841_;
}
else
{
uint8_t v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4842_ = 0;
v___x_4843_ = lean_box(v___x_4842_);
v___x_4844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4843_);
return v___x_4844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_){
_start:
{
uint8_t v_____do__lift_1654__boxed_4849_; lean_object* v_res_4850_; 
v_____do__lift_1654__boxed_4849_ = lean_unbox(v_____do__lift_4845_);
v_res_4850_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v_____do__lift_1654__boxed_4849_, v___y_4846_, v___y_4847_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(lean_object* v_as_4851_, size_t v_i_4852_, size_t v_stop_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
uint8_t v___x_4861_; 
v___x_4861_ = lean_usize_dec_eq(v_i_4852_, v_stop_4853_);
if (v___x_4861_ == 0)
{
uint8_t v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4862_ = 1;
v___x_4863_ = lean_array_uget_borrowed(v_as_4851_, v_i_4852_);
lean_inc(v___x_4863_);
v___x_4864_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__1___redArg(v___x_4863_, v___y_4855_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4874_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4867_ = v___x_4864_;
v_isShared_4868_ = v_isSharedCheck_4874_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4864_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4874_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
uint8_t v___x_4869_; 
v___x_4869_ = lean_unbox(v_a_4865_);
lean_dec(v_a_4865_);
if (v___x_4869_ == 0)
{
lean_object* v___x_4870_; lean_object* v___x_4872_; 
v___x_4870_ = lean_box(v___x_4862_);
if (v_isShared_4868_ == 0)
{
lean_ctor_set(v___x_4867_, 0, v___x_4870_);
v___x_4872_ = v___x_4867_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v___x_4870_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
else
{
lean_del_object(v___x_4867_);
goto v___jp_4857_;
}
}
}
else
{
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4884_; 
v_a_4875_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4877_ = v___x_4864_;
v_isShared_4878_ = v_isSharedCheck_4884_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_a_4875_);
lean_dec(v___x_4864_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4884_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
uint8_t v___x_4879_; 
v___x_4879_ = lean_unbox(v_a_4875_);
lean_dec(v_a_4875_);
if (v___x_4879_ == 0)
{
lean_del_object(v___x_4877_);
goto v___jp_4857_;
}
else
{
lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4880_ = lean_box(v___x_4862_);
if (v_isShared_4878_ == 0)
{
lean_ctor_set_tag(v___x_4877_, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4880_);
v___x_4882_ = v___x_4877_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
else
{
return v___x_4864_;
}
}
}
else
{
uint8_t v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4885_ = 0;
v___x_4886_ = lean_box(v___x_4885_);
v___x_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
return v___x_4887_;
}
v___jp_4857_:
{
size_t v___x_4858_; size_t v___x_4859_; 
v___x_4858_ = ((size_t)1ULL);
v___x_4859_ = lean_usize_add(v_i_4852_, v___x_4858_);
v_i_4852_ = v___x_4859_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2___boxed(lean_object* v_as_4888_, lean_object* v_i_4889_, lean_object* v_stop_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
size_t v_i_boxed_4894_; size_t v_stop_boxed_4895_; lean_object* v_res_4896_; 
v_i_boxed_4894_ = lean_unbox_usize(v_i_4889_);
lean_dec(v_i_4889_);
v_stop_boxed_4895_ = lean_unbox_usize(v_stop_4890_);
lean_dec(v_stop_4890_);
v_res_4896_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(v_as_4888_, v_i_boxed_4894_, v_stop_boxed_4895_, v___y_4891_, v___y_4892_);
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec_ref(v_as_4888_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(lean_object* v_as_4897_, size_t v_sz_4898_, size_t v_i_4899_, lean_object* v_b_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_){
_start:
{
uint8_t v___x_4904_; 
v___x_4904_ = lean_usize_dec_lt(v_i_4899_, v_sz_4898_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4905_; 
v___x_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4905_, 0, v_b_4900_);
return v___x_4905_;
}
else
{
lean_object* v_a_4906_; lean_object* v___x_4907_; 
v_a_4906_ = lean_array_uget_borrowed(v_as_4897_, v_i_4899_);
lean_inc(v_a_4906_);
v___x_4907_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstance(v_a_4906_, v___y_4901_, v___y_4902_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v___x_4908_; size_t v___x_4909_; size_t v___x_4910_; 
lean_dec_ref_known(v___x_4907_, 1);
v___x_4908_ = lean_box(0);
v___x_4909_ = ((size_t)1ULL);
v___x_4910_ = lean_usize_add(v_i_4899_, v___x_4909_);
v_i_4899_ = v___x_4910_;
v_b_4900_ = v___x_4908_;
goto _start;
}
else
{
return v___x_4907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0___boxed(lean_object* v_as_4912_, lean_object* v_sz_4913_, lean_object* v_i_4914_, lean_object* v_b_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
size_t v_sz_boxed_4919_; size_t v_i_boxed_4920_; lean_object* v_res_4921_; 
v_sz_boxed_4919_ = lean_unbox_usize(v_sz_4913_);
lean_dec(v_sz_4913_);
v_i_boxed_4920_ = lean_unbox_usize(v_i_4914_);
lean_dec(v_i_4914_);
v_res_4921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(v_as_4912_, v_sz_boxed_4919_, v_i_boxed_4920_, v_b_4915_, v___y_4916_, v___y_4917_);
lean_dec(v___y_4917_);
lean_dec_ref(v___y_4916_);
lean_dec_ref(v_as_4912_);
return v_res_4921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler(lean_object* v_declNames_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_){
_start:
{
lean_object* v___y_4950_; lean_object* v___x_4953_; lean_object* v___x_4954_; uint8_t v___x_4955_; 
v___x_4953_ = lean_unsigned_to_nat(0u);
v___x_4954_ = lean_array_get_size(v_declNames_4922_);
v___x_4955_ = lean_nat_dec_lt(v___x_4953_, v___x_4954_);
if (v___x_4955_ == 0)
{
lean_object* v___x_4956_; 
v___x_4956_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v___x_4955_, v_a_4923_, v_a_4924_);
v___y_4950_ = v___x_4956_;
goto v___jp_4949_;
}
else
{
if (v___x_4955_ == 0)
{
goto v___jp_4926_;
}
else
{
size_t v___x_4957_; size_t v___x_4958_; lean_object* v___x_4959_; 
v___x_4957_ = ((size_t)0ULL);
v___x_4958_ = lean_usize_of_nat(v___x_4954_);
v___x_4959_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__2(v_declNames_4922_, v___x_4957_, v___x_4958_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v_a_4960_; uint8_t v___x_4961_; lean_object* v___x_4962_; 
v_a_4960_ = lean_ctor_get(v___x_4959_, 0);
lean_inc(v_a_4960_);
lean_dec_ref_known(v___x_4959_, 1);
v___x_4961_ = lean_unbox(v_a_4960_);
lean_dec(v_a_4960_);
v___x_4962_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___lam__0(v___x_4961_, v_a_4923_, v_a_4924_);
v___y_4950_ = v___x_4962_;
goto v___jp_4949_;
}
else
{
v___y_4950_ = v___x_4959_;
goto v___jp_4949_;
}
}
}
v___jp_4926_:
{
lean_object* v___x_4927_; size_t v_sz_4928_; size_t v___x_4929_; lean_object* v___x_4930_; 
v___x_4927_ = lean_box(0);
v_sz_4928_ = lean_array_size(v_declNames_4922_);
v___x_4929_ = ((size_t)0ULL);
v___x_4930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler_spec__0(v_declNames_4922_, v_sz_4928_, v___x_4929_, v___x_4927_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4939_; 
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4939_ == 0)
{
lean_object* v_unused_4940_; 
v_unused_4940_ = lean_ctor_get(v___x_4930_, 0);
lean_dec(v_unused_4940_);
v___x_4932_ = v___x_4930_;
v_isShared_4933_ = v_isSharedCheck_4939_;
goto v_resetjp_4931_;
}
else
{
lean_dec(v___x_4930_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4939_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
uint8_t v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4937_; 
v___x_4934_ = 1;
v___x_4935_ = lean_box(v___x_4934_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4935_);
v___x_4937_ = v___x_4932_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4935_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
else
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
v_a_4941_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4930_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4930_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
v___jp_4949_:
{
if (lean_obj_tag(v___y_4950_) == 0)
{
lean_object* v_a_4951_; uint8_t v___x_4952_; 
v_a_4951_ = lean_ctor_get(v___y_4950_, 0);
v___x_4952_ = lean_unbox(v_a_4951_);
if (v___x_4952_ == 0)
{
return v___y_4950_;
}
else
{
lean_dec_ref_known(v___y_4950_, 1);
goto v___jp_4926_;
}
}
else
{
return v___y_4950_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler___boxed(lean_object* v_declNames_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceHandler(v_declNames_4963_, v_a_4964_, v_a_4965_);
lean_dec(v_a_4965_);
lean_dec_ref(v_a_4964_);
lean_dec_ref(v_declNames_4963_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5004_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqHeader___closed__0));
v___x_5005_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_));
v___x_5006_ = l_Lean_Elab_registerDerivingHandler(v___x_5004_, v___x_5005_);
if (lean_obj_tag(v___x_5006_) == 0)
{
lean_object* v___x_5007_; uint8_t v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
lean_dec_ref_known(v___x_5006_, 1);
v___x_5007_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_mkBEqInstanceCmds___closed__0));
v___x_5008_ = 0;
v___x_5009_ = ((lean_object*)(l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_));
v___x_5010_ = l_Lean_registerTraceClass(v___x_5007_, v___x_5008_, v___x_5009_);
return v___x_5010_;
}
else
{
return v___x_5006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2____boxed(lean_object* v_a_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_993467269____hygCtx___hyg_2_();
return v_res_5012_;
}
}
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_BEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Elab_Deriving_BEq_0__Lean_Elab_Deriving_BEq_initFn_00___x40_Lean_Elab_Deriving_BEq_3666926342____hygCtx___hyg_4_();
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
