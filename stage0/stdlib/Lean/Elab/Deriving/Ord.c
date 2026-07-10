// Lean compiler output
// Module: Lean.Elab.Deriving.Ord
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
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_occursOrInType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Lean_mkCasesOnSameCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ord"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "linear_construction_threshold"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 127, 229, 132, 157, 42, 70, 134)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(58, 105, 173, 43, 143, 234, 178, 2)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(119, 157, 91, 192, 251, 142, 191, 166)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 350, .m_capacity = 350, .m_length = 349, .m_data = "If the inductive data type has this many or more constructors, use a different implementation for implementing `Ord` that avoids the quadratic code size produced by the default implementation.\n\nThe alternative construction compiles to less efficient code in some cases, so by default it is only used for inductive types with 10 or more constructors."};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ord"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(234, 29, 188, 163, 17, 185, 131, 241)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(235, 228, 53, 108, 241, 27, 196, 104)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(182, 7, 46, 207, 203, 113, 203, 236)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(106, 109, 90, 201, 238, 184, 42, 89)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__19_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(231, 74, 63, 253, 21, 218, 53, 222)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__19_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__19_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__deriving_ord_linear__construction__threshold;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(47, 34, 14, 190, 177, 218, 16, 31)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Ordering.then"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Ordering"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(97, 170, 41, 107, 24, 174, 163, 92)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__11_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__9_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__11_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__13_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__15_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__17_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__20_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(134, 215, 124, 37, 166, 123, 51, 213)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__25_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__26_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__28_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__30_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__31_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__28_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__31_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__32_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__25_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__32_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(47, 34, 14, 190, 177, 218, 16, 31)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34_value),LEAN_SCALAR_PTR_LITERAL(241, 180, 168, 39, 68, 69, 153, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__38_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inaccessible"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 90, 7, 119, 108, 205, 19, 233)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Ordering.eq"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 150, 86, 2, 28, 163, 164, 77)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15_value),LEAN_SCALAR_PTR_LITERAL(151, 65, 236, 10, 147, 23, 177, 156)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Ordering.lt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Ordering.gt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__26 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__26_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__28 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__28_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__28_value),LEAN_SCALAR_PTR_LITERAL(117, 227, 205, 91, 93, 250, 7, 4)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__30 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__30_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__31 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__31_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__32 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__32_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__30_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__32_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__33 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__33_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0_value;
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1_value;
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Elab.Deriving.Ord"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Elab.Deriving.Ord.0.Lean.Elab.Deriving.Ord.mkMatchNew"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: header.targetNames.size == 2\n\n  "};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "match_on_same_ctor"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 38, 237, 47, 106, 10, 11, 248)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__6_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__28_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__14_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__25_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__15_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__23_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__24_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Nat.compare_eq_eq.mp"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__26_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__28 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__28_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "compare_eq_eq"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__29_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__30 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__28_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__29_value),LEAN_SCALAR_PTR_LITERAL(242, 151, 26, 225, 153, 203, 91, 119)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__30_value),LEAN_SCALAR_PTR_LITERAL(94, 11, 29, 173, 18, 99, 159, 69)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__28_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__29_value),LEAN_SCALAR_PTR_LITERAL(242, 151, 26, 225, 153, 203, 91, 119)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__33_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__34 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__35 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__35_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__39 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__39_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__40 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__40_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__5_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__8_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__12_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__16_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__18_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__20_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__23_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__24_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "set_option"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2_value),LEAN_SCALAR_PTR_LITERAL(216, 223, 149, 245, 150, 86, 134, 198)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "match.ignoreUnusedAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ignoreUnusedAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 5, 219, 45, 43, 52, 169, 192)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__6_value),LEAN_SCALAR_PTR_LITERAL(49, 254, 67, 85, 227, 127, 91, 187)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(3, 185, 255, 214, 49, 16, 173, 251)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__11_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__13_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__14_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "method_specs"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16_value),LEAN_SCALAR_PTR_LITERAL(101, 159, 225, 215, 58, 146, 25, 204)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__8_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "x.ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(2, 247, 218, 116, 51, 159, 161, 152)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "y.ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(85, 37, 232, 186, 208, 254, 208, 112)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(214, 245, 77, 140, 236, 123, 248, 43)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 87, 41, 84, 80, 186, 228, 139)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(214, 146, 61, 148, 52, 127, 164, 158)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(54, 226, 227, 81, 35, 13, 185, 126)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 135, 205, 158, 42, 30, 240, 37)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 41, 211, 152, 255, 207, 100, 126)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 200, 248, 195, 255, 104, 182, 0)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(73, 190, 197, 108, 143, 88, 227, 65)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(47, 199, 3, 241, 107, 15, 45, 213)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 15, 148, 183, 57, 172, 17, 87)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1187715530) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(253, 121, 178, 8, 160, 220, 233, 66)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 65, 24, 154, 152, 230, 188, 253)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(50, 66, 188, 46, 171, 180, 95, 99)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(11, 83, 81, 67, 51, 241, 247, 37)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_28_, lean_object* v_decl_29_, lean_object* v_ref_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0(v_name_28_, v_decl_29_, v_ref_30_);
lean_dec_ref(v_decl_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_79_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_80_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__19_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_81_ = l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0(v___x_78_, v___x_79_, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4____boxed(lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_();
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader(lean_object* v_indVal_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_95_ = lean_unsigned_to_nat(2u);
v___x_96_ = l_Lean_Elab_Deriving_mkHeader(v___x_94_, v___x_95_, v_indVal_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___boxed(lean_object* v_indVal_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader(v_indVal_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0(lean_object* v_k_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v_b_109_, lean_object* v_c_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___x_116_; 
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
v___x_116_ = lean_apply_9(v_k_106_, v_b_109_, v_c_110_, v___y_107_, v___y_108_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, lean_box(0));
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0___boxed(lean_object* v_k_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v_b_120_, lean_object* v_c_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0(v_k_117_, v___y_118_, v___y_119_, v_b_120_, v_c_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(lean_object* v_type_128_, lean_object* v_k_129_, uint8_t v_cleanupAnnotations_130_, uint8_t v_whnfType_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___f_139_; lean_object* v___x_140_; 
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
v___f_139_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_139_, 0, v_k_129_);
lean_closure_set(v___f_139_, 1, v___y_132_);
lean_closure_set(v___f_139_, 2, v___y_133_);
v___x_140_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_128_, v___f_139_, v_cleanupAnnotations_130_, v_whnfType_131_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
if (lean_obj_tag(v___x_140_) == 0)
{
return v___x_140_;
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object* v_type_149_, lean_object* v_k_150_, lean_object* v_cleanupAnnotations_151_, lean_object* v_whnfType_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_160_; uint8_t v_whnfType_boxed_161_; lean_object* v_res_162_; 
v_cleanupAnnotations_boxed_160_ = lean_unbox(v_cleanupAnnotations_151_);
v_whnfType_boxed_161_ = lean_unbox(v_whnfType_152_);
v_res_162_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_149_, v_k_150_, v_cleanupAnnotations_boxed_160_, v_whnfType_boxed_161_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5(lean_object* v_00_u03b1_163_, lean_object* v_type_164_, lean_object* v_k_165_, uint8_t v_cleanupAnnotations_166_, uint8_t v_whnfType_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_164_, v_k_165_, v_cleanupAnnotations_166_, v_whnfType_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___boxed(lean_object* v_00_u03b1_176_, lean_object* v_type_177_, lean_object* v_k_178_, lean_object* v_cleanupAnnotations_179_, lean_object* v_whnfType_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_188_; uint8_t v_whnfType_boxed_189_; lean_object* v_res_190_; 
v_cleanupAnnotations_boxed_188_ = lean_unbox(v_cleanupAnnotations_179_);
v_whnfType_boxed_189_ = lean_unbox(v_whnfType_180_);
v_res_190_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5(v_00_u03b1_176_, v_type_177_, v_k_178_, v_cleanupAnnotations_boxed_188_, v_whnfType_boxed_189_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(size_t v_sz_191_, size_t v_i_192_, lean_object* v_bs_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_lt(v_i_192_, v_sz_191_);
if (v___x_194_ == 0)
{
return v_bs_193_;
}
else
{
lean_object* v_v_195_; lean_object* v___x_196_; lean_object* v_bs_x27_197_; size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v_v_195_ = lean_array_uget(v_bs_193_, v_i_192_);
v___x_196_ = lean_unsigned_to_nat(0u);
v_bs_x27_197_ = lean_array_uset(v_bs_193_, v_i_192_, v___x_196_);
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_add(v_i_192_, v___x_198_);
v___x_200_ = lean_array_uset(v_bs_x27_197_, v_i_192_, v_v_195_);
v_i_192_ = v___x_199_;
v_bs_193_ = v___x_200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1___boxed(lean_object* v_sz_202_, lean_object* v_i_203_, lean_object* v_bs_204_){
_start:
{
size_t v_sz_boxed_205_; size_t v_i_boxed_206_; lean_object* v_res_207_; 
v_sz_boxed_205_ = lean_unbox_usize(v_sz_202_);
lean_dec(v_sz_202_);
v_i_boxed_206_ = lean_unbox_usize(v_i_203_);
lean_dec(v_i_203_);
v_res_207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_boxed_205_, v_i_boxed_206_, v_bs_204_);
return v_res_207_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__4));
v___x_218_ = l_String_toRawSubstring_x27(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22));
v___x_256_ = l_String_toRawSubstring_x27(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34));
v___x_287_ = l_String_toRawSubstring_x27(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0(uint8_t v___x_300_, lean_object* v___x_301_, lean_object* v___x_302_, lean_object* v_snd_303_, lean_object* v_rhs_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_ref_312_; lean_object* v_quotContext_313_; lean_object* v_currMacroScope_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_ref_312_ = lean_ctor_get(v___y_309_, 5);
v_quotContext_313_ = lean_ctor_get(v___y_309_, 10);
v_currMacroScope_314_ = lean_ctor_get(v___y_309_, 11);
v___x_315_ = l_Lean_SourceInfo_fromRef(v_ref_312_, v___x_300_);
v___x_316_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_317_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5);
v___x_318_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8));
lean_inc_n(v_currMacroScope_314_, 3);
lean_inc_n(v_quotContext_313_, 3);
v___x_319_ = l_Lean_addMacroScope(v_quotContext_313_, v___x_318_, v_currMacroScope_314_);
v___x_320_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12));
lean_inc_n(v___x_315_, 11);
v___x_321_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_321_, 0, v___x_315_);
lean_ctor_set(v___x_321_, 1, v___x_317_);
lean_ctor_set(v___x_321_, 2, v___x_319_);
lean_ctor_set(v___x_321_, 3, v___x_320_);
v___x_322_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_323_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16));
v___x_324_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_325_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_315_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_328_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_329_ = lean_box(0);
v___x_330_ = l_Lean_addMacroScope(v_quotContext_313_, v___x_329_, v_currMacroScope_314_);
v___x_331_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33));
v___x_332_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_332_, 0, v___x_315_);
lean_ctor_set(v___x_332_, 1, v___x_328_);
lean_ctor_set(v___x_332_, 2, v___x_330_);
lean_ctor_set(v___x_332_, 3, v___x_331_);
v___x_333_ = l_Lean_Syntax_node1(v___x_315_, v___x_327_, v___x_332_);
v___x_334_ = l_Lean_Syntax_node2(v___x_315_, v___x_324_, v___x_326_, v___x_333_);
v___x_335_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_336_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
v___x_337_ = l_Lean_addMacroScope(v_quotContext_313_, v___x_336_, v_currMacroScope_314_);
v___x_338_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39));
v___x_339_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_339_, 0, v___x_315_);
lean_ctor_set(v___x_339_, 1, v___x_335_);
lean_ctor_set(v___x_339_, 2, v___x_337_);
lean_ctor_set(v___x_339_, 3, v___x_338_);
v___x_340_ = l_Lean_Syntax_node2(v___x_315_, v___x_322_, v___x_301_, v___x_302_);
v___x_341_ = l_Lean_Syntax_node2(v___x_315_, v___x_316_, v___x_339_, v___x_340_);
v___x_342_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_315_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = l_Lean_Syntax_node3(v___x_315_, v___x_323_, v___x_334_, v___x_341_, v___x_343_);
v___x_345_ = l_Lean_Syntax_node2(v___x_315_, v___x_322_, v___x_344_, v_rhs_304_);
v___x_346_ = l_Lean_Syntax_node2(v___x_315_, v___x_316_, v___x_321_, v___x_345_);
lean_inc(v___y_310_);
lean_inc_ref(v___y_309_);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
v___x_347_ = lean_apply_8(v_snd_303_, v___x_346_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, lean_box(0));
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___boxed(lean_object* v___x_348_, lean_object* v___x_349_, lean_object* v___x_350_, lean_object* v_snd_351_, lean_object* v_rhs_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
uint8_t v___x_49774__boxed_360_; lean_object* v_res_361_; 
v___x_49774__boxed_360_ = lean_unbox(v___x_348_);
v_res_361_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0(v___x_49774__boxed_360_, v___x_349_, v___x_350_, v_snd_351_, v_rhs_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(lean_object* v_upperBound_382_, lean_object* v___x_383_, lean_object* v_xs_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_b_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_a_394_; uint8_t v___x_398_; 
v___x_398_ = lean_nat_dec_lt(v_a_386_, v_upperBound_382_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec(v_a_386_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v_b_387_);
return v___x_399_;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_400_ = l_Lean_instInhabitedExpr;
v___x_401_ = lean_nat_add(v___x_383_, v_a_386_);
v___x_402_ = lean_array_get_borrowed(v___x_400_, v_xs_384_, v___x_401_);
lean_dec(v___x_401_);
lean_inc(v___x_402_);
v___x_403_ = l_Lean_Meta_isProof(v___x_402_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_snd_404_; lean_object* v_a_405_; uint8_t v___x_406_; 
v_snd_404_ = lean_ctor_get(v_b_387_, 1);
lean_inc(v_snd_404_);
v_a_405_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_403_, 1);
v___x_406_ = lean_unbox(v_a_405_);
if (v___x_406_ == 0)
{
lean_object* v_fst_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_482_; 
v_fst_407_ = lean_ctor_get(v_b_387_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v_b_387_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v_b_387_, 1);
lean_dec(v_unused_483_);
v___x_409_ = v_b_387_;
v_isShared_410_ = v_isSharedCheck_482_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_fst_407_);
lean_dec(v_b_387_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_482_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_fst_411_; lean_object* v_snd_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_481_; 
v_fst_411_ = lean_ctor_get(v_snd_404_, 0);
v_snd_412_ = lean_ctor_get(v_snd_404_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_snd_404_);
if (v_isSharedCheck_481_ == 0)
{
v___x_414_ = v_snd_404_;
v_isShared_415_ = v_isSharedCheck_481_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_snd_412_);
lean_inc(v_fst_411_);
lean_dec(v_snd_404_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_481_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_lctx_416_; uint8_t v___x_417_; 
v_lctx_416_ = lean_ctor_get(v___y_388_, 2);
lean_inc(v___x_402_);
lean_inc_ref(v_lctx_416_);
v___x_417_ = l_Lean_Meta_occursOrInType(v_lctx_416_, v___x_402_, v_a_385_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_a_405_);
v___x_418_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__1));
v___x_419_ = l_Lean_Core_mkFreshUserName(v___x_418_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_419_, 1);
v___x_421_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__3));
v___x_422_ = l_Lean_Core_mkFreshUserName(v___x_421_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___f_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_422_, 1);
v___x_424_ = l_Lean_mkIdent(v_a_420_);
v___x_425_ = l_Lean_mkIdent(v_a_423_);
v___x_426_ = lean_box(v___x_417_);
lean_inc(v___x_425_);
lean_inc(v___x_424_);
v___f_427_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_427_, 0, v___x_426_);
lean_closure_set(v___f_427_, 1, v___x_424_);
lean_closure_set(v___f_427_, 2, v___x_425_);
lean_closure_set(v___f_427_, 3, v_snd_412_);
v___x_428_ = lean_array_push(v_fst_407_, v___x_424_);
v___x_429_ = lean_array_push(v_fst_411_, v___x_425_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___f_427_);
lean_ctor_set(v___x_414_, 0, v___x_429_);
v___x_431_ = v___x_414_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___f_427_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___x_431_);
lean_ctor_set(v___x_409_, 0, v___x_428_);
v___x_433_ = v___x_409_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
v_a_394_ = v___x_433_;
goto v___jp_393_;
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec(v_a_420_);
lean_del_object(v___x_414_);
lean_dec(v_snd_412_);
lean_dec(v_fst_411_);
lean_del_object(v___x_409_);
lean_dec(v_fst_407_);
lean_dec(v_a_386_);
v_a_436_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_422_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_422_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_del_object(v___x_414_);
lean_dec(v_snd_412_);
lean_dec(v_fst_411_);
lean_del_object(v___x_409_);
lean_dec(v_fst_407_);
lean_dec(v_a_386_);
v_a_444_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_419_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_419_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__1));
v___x_453_ = l_Lean_Core_mkFreshUserName(v___x_452_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v_ref_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
v_ref_455_ = lean_ctor_get(v___y_390_, 5);
v___x_456_ = l_Lean_mkIdent(v_a_454_);
lean_inc(v___x_456_);
v___x_457_ = lean_array_push(v_fst_407_, v___x_456_);
v___x_458_ = lean_unbox(v_a_405_);
lean_dec(v_a_405_);
v___x_459_ = l_Lean_SourceInfo_fromRef(v_ref_455_, v___x_458_);
v___x_460_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5));
v___x_461_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__6));
lean_inc_n(v___x_459_, 2);
v___x_462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_459_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_459_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = l_Lean_Syntax_node3(v___x_459_, v___x_460_, v___x_462_, v___x_456_, v___x_464_);
v___x_466_ = lean_array_push(v_fst_411_, v___x_465_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_466_);
v___x_468_ = v___x_414_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_snd_412_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___x_468_);
lean_ctor_set(v___x_409_, 0, v___x_457_);
v___x_470_ = v___x_409_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
v_a_394_ = v___x_470_;
goto v___jp_393_;
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_del_object(v___x_414_);
lean_dec(v_snd_412_);
lean_dec(v_fst_411_);
lean_del_object(v___x_409_);
lean_dec(v_fst_407_);
lean_dec(v_a_405_);
lean_dec(v_a_386_);
v_a_473_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_453_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_453_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
}
else
{
lean_object* v_fst_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_509_; 
lean_dec(v_a_405_);
v_fst_484_ = lean_ctor_get(v_b_387_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_b_387_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v_b_387_, 1);
lean_dec(v_unused_510_);
v___x_486_ = v_b_387_;
v_isShared_487_ = v_isSharedCheck_509_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_fst_484_);
lean_dec(v_b_387_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_509_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v_fst_488_; lean_object* v_snd_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_508_; 
v_fst_488_ = lean_ctor_get(v_snd_404_, 0);
v_snd_489_ = lean_ctor_get(v_snd_404_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_snd_404_);
if (v_isSharedCheck_508_ == 0)
{
v___x_491_ = v_snd_404_;
v_isShared_492_ = v_isSharedCheck_508_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_snd_489_);
lean_inc(v_fst_488_);
lean_dec(v_snd_404_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_508_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v_ref_493_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v_ref_493_ = lean_ctor_get(v___y_390_, 5);
v___x_494_ = 0;
v___x_495_ = l_Lean_SourceInfo_fromRef(v_ref_493_, v___x_494_);
v___x_496_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_497_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_495_);
v___x_498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_495_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_Syntax_node1(v___x_495_, v___x_496_, v___x_498_);
lean_inc(v___x_499_);
v___x_500_ = lean_array_push(v_fst_484_, v___x_499_);
v___x_501_ = lean_array_push(v_fst_488_, v___x_499_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_501_);
v___x_503_ = v___x_491_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_snd_489_);
v___x_503_ = v_reuseFailAlloc_507_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_505_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v___x_503_);
lean_ctor_set(v___x_486_, 0, v___x_500_);
v___x_505_ = v___x_486_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
v_a_394_ = v___x_505_;
goto v___jp_393_;
}
}
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref(v_b_387_);
lean_dec(v_a_386_);
v_a_511_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_403_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_403_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
v___jp_393_:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_nat_add(v_a_386_, v___x_395_);
lean_dec(v_a_386_);
v_a_386_ = v___x_396_;
v_b_387_ = v_a_394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object* v_upperBound_519_, lean_object* v___x_520_, lean_object* v_xs_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_b_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(v_upperBound_519_, v___x_520_, v_xs_521_, v_a_522_, v_a_523_, v_b_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec_ref(v_a_522_);
lean_dec_ref(v_xs_521_);
lean_dec(v___x_520_);
lean_dec(v_upperBound_519_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(lean_object* v_upperBound_531_, lean_object* v_a_532_, lean_object* v_b_533_, lean_object* v___y_534_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = lean_nat_dec_lt(v_a_532_, v_upperBound_531_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_dec(v_a_532_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v_b_533_);
return v___x_537_;
}
else
{
lean_object* v_ref_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_ref_538_ = lean_ctor_get(v___y_534_, 5);
v___x_539_ = 0;
v___x_540_ = l_Lean_SourceInfo_fromRef(v_ref_538_, v___x_539_);
v___x_541_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_542_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_540_);
v___x_543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_540_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_Syntax_node1(v___x_540_, v___x_541_, v___x_543_);
v___x_545_ = lean_array_push(v_b_533_, v___x_544_);
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = lean_nat_add(v_a_532_, v___x_546_);
lean_dec(v_a_532_);
v_a_532_ = v___x_547_;
v_b_533_ = v___x_545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object* v_upperBound_549_, lean_object* v_a_550_, lean_object* v_b_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(v_upperBound_549_, v_a_550_, v_b_551_, v___y_552_);
lean_dec_ref(v___y_552_);
lean_dec(v_upperBound_549_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(lean_object* v_upperBound_555_, lean_object* v_a_556_, lean_object* v_b_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___x_560_; 
v___x_560_ = lean_nat_dec_lt(v_a_556_, v_upperBound_555_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
lean_dec(v_a_556_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_b_557_);
return v___x_561_;
}
else
{
lean_object* v_fst_562_; lean_object* v_snd_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_582_; 
v_fst_562_ = lean_ctor_get(v_b_557_, 0);
v_snd_563_ = lean_ctor_get(v_b_557_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v_b_557_);
if (v_isSharedCheck_582_ == 0)
{
v___x_565_ = v_b_557_;
v_isShared_566_ = v_isSharedCheck_582_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snd_563_);
lean_inc(v_fst_562_);
lean_dec(v_b_557_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_582_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v_ref_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v_ref_567_ = lean_ctor_get(v___y_558_, 5);
v___x_568_ = 0;
v___x_569_ = l_Lean_SourceInfo_fromRef(v_ref_567_, v___x_568_);
v___x_570_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_571_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_569_);
v___x_572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_569_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Lean_Syntax_node1(v___x_569_, v___x_570_, v___x_572_);
lean_inc(v___x_573_);
v___x_574_ = lean_array_push(v_fst_562_, v___x_573_);
v___x_575_ = lean_array_push(v_snd_563_, v___x_573_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v___x_575_);
lean_ctor_set(v___x_565_, 0, v___x_574_);
v___x_577_ = v___x_565_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_a_556_, v___x_578_);
lean_dec(v_a_556_);
v_a_556_ = v___x_579_;
v_b_557_ = v___x_577_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_583_, lean_object* v_a_584_, lean_object* v_b_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_583_, v_a_584_, v_b_585_, v___y_586_);
lean_dec_ref(v___y_586_);
lean_dec(v_upperBound_583_);
return v_res_588_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0));
v___x_591_ = l_String_toRawSubstring_x27(v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11(void){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Array_mkArray0(lean_box(0));
return v___x_614_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13));
v___x_618_ = l_Lean_mkAtom(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19));
v___x_629_ = l_String_toRawSubstring_x27(v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__26));
v___x_646_ = l_String_toRawSubstring_x27(v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2(lean_object* v_indVal_662_, lean_object* v___x_663_, lean_object* v_alts_664_, lean_object* v___f_665_, lean_object* v_numFields_666_, lean_object* v___f_667_, lean_object* v_head_668_, lean_object* v_xs_669_, lean_object* v_type_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Core_betaReduce(v_type_670_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v_numParams_680_; lean_object* v_numIndices_681_; lean_object* v___x_682_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_678_, 1);
v_numParams_680_ = lean_ctor_get(v_indVal_662_, 1);
v_numIndices_681_ = lean_ctor_get(v_indVal_662_, 2);
lean_inc_ref(v_alts_664_);
lean_inc(v___x_663_);
v___x_682_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(v_numIndices_681_, v___x_663_, v_alts_664_, v___y_675_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
lean_inc_ref(v_alts_664_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_alts_664_);
lean_ctor_set(v___x_684_, 1, v_alts_664_);
lean_inc(v___x_663_);
v___x_685_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(v_numParams_680_, v___x_663_, v___x_684_, v___y_675_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v_fst_687_; lean_object* v_snd_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_899_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 1);
v_fst_687_ = lean_ctor_get(v_a_686_, 0);
v_snd_688_ = lean_ctor_get(v_a_686_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_a_686_);
if (v_isSharedCheck_899_ == 0)
{
v___x_690_ = v_a_686_;
v_isShared_691_ = v_isSharedCheck_899_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_snd_688_);
lean_inc(v_fst_687_);
lean_dec(v_a_686_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_899_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___f_665_);
lean_ctor_set(v___x_690_, 0, v_snd_688_);
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_snd_688_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___f_665_);
v___x_693_ = v_reuseFailAlloc_898_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_fst_687_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(v_numFields_666_, v_numParams_680_, v_xs_669_, v_a_679_, v___x_663_, v___x_694_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v_a_679_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v_ref_697_; lean_object* v_quotContext_698_; lean_object* v_currMacroScope_699_; lean_object* v___x_700_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v_ref_697_ = lean_ctor_get(v___y_675_, 5);
v_quotContext_698_ = lean_ctor_get(v___y_675_, 10);
v_currMacroScope_699_ = lean_ctor_get(v___y_675_, 11);
lean_inc_ref(v___f_667_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_700_ = lean_apply_7(v___f_667_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, lean_box(0));
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
lean_inc_ref(v___f_667_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_702_ = lean_apply_7(v___f_667_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, lean_box(0));
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
lean_inc_ref(v___f_667_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_704_ = lean_apply_7(v___f_667_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, lean_box(0));
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
lean_inc_ref(v___f_667_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_706_ = lean_apply_7(v___f_667_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, lean_box(0));
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_snd_707_; lean_object* v_a_708_; lean_object* v_fst_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_856_; 
v_snd_707_ = lean_ctor_get(v_a_696_, 1);
lean_inc(v_snd_707_);
v_a_708_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_706_, 1);
v_fst_709_ = lean_ctor_get(v_a_696_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_a_696_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v_a_696_, 1);
lean_dec(v_unused_857_);
v___x_711_ = v_a_696_;
v_isShared_712_ = v_isSharedCheck_856_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_fst_709_);
lean_dec(v_a_696_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_856_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_855_; 
v_fst_713_ = lean_ctor_get(v_snd_707_, 0);
v_snd_714_ = lean_ctor_get(v_snd_707_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_snd_707_);
if (v_isSharedCheck_855_ == 0)
{
v___x_716_ = v_snd_707_;
v_isShared_717_ = v_isSharedCheck_855_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_inc(v_fst_713_);
lean_dec(v_snd_707_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_855_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_718_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1);
v___x_719_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3));
lean_inc(v_currMacroScope_699_);
lean_inc(v_quotContext_698_);
v___x_720_ = l_Lean_addMacroScope(v_quotContext_698_, v___x_719_, v_currMacroScope_699_);
v___x_721_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7));
v___x_722_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_722_, 0, v_a_708_);
lean_ctor_set(v___x_722_, 1, v___x_718_);
lean_ctor_set(v___x_722_, 2, v___x_720_);
lean_ctor_set(v___x_722_, 3, v___x_721_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_723_ = lean_apply_8(v_snd_714_, v___x_722_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, lean_box(0));
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
lean_inc_ref(v___f_667_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_725_ = lean_apply_7(v___f_667_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, lean_box(0));
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
lean_inc_ref(v___f_667_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_727_ = lean_apply_7(v___f_667_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, lean_box(0));
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_729_ = lean_apply_7(v___f_667_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, lean_box(0));
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_822_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_822_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_822_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_822_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
uint8_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_734_ = 0;
v___x_735_ = l_Lean_SourceInfo_fromRef(v_ref_697_, v___x_734_);
v___x_736_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8));
lean_inc(v___x_735_);
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 2);
lean_ctor_set(v___x_716_, 1, v___x_736_);
lean_ctor_set(v___x_716_, 0, v___x_735_);
v___x_738_ = v___x_716_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_736_);
v___x_738_ = v_reuseFailAlloc_821_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_739_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_740_ = l_Lean_mkIdent(v_head_668_);
lean_inc(v_a_701_);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 2);
lean_ctor_set(v___x_711_, 1, v___x_736_);
lean_ctor_set(v___x_711_, 0, v_a_701_);
v___x_742_ = v___x_711_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_701_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_736_);
v___x_742_ = v_reuseFailAlloc_820_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; size_t v_sz_767_; lean_object* v___x_768_; size_t v_sz_769_; size_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; size_t v_sz_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_743_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10));
lean_inc(v___x_740_);
lean_inc_n(v___x_735_, 2);
v___x_744_ = l_Lean_Syntax_node2(v___x_735_, v___x_743_, v___x_738_, v___x_740_);
lean_inc_n(v_a_701_, 2);
v___x_745_ = l_Lean_Syntax_node2(v_a_701_, v___x_743_, v___x_742_, v___x_740_);
v___x_746_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_747_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_748_ = l_Array_append___redArg(v___x_747_, v_fst_709_);
lean_dec(v_fst_709_);
v___x_749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_749_, 0, v___x_735_);
lean_ctor_set(v___x_749_, 1, v___x_746_);
lean_ctor_set(v___x_749_, 2, v___x_748_);
v___x_750_ = l_Array_append___redArg(v___x_747_, v_fst_713_);
lean_dec(v_fst_713_);
v___x_751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_751_, 0, v_a_701_);
lean_ctor_set(v___x_751_, 1, v___x_746_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
v___x_752_ = l_Lean_Syntax_node2(v___x_735_, v___x_739_, v___x_744_, v___x_749_);
v___x_753_ = l_Lean_Syntax_node2(v_a_701_, v___x_739_, v___x_745_, v___x_751_);
v___x_754_ = lean_unsigned_to_nat(2u);
v___x_755_ = lean_mk_empty_array_with_capacity(v___x_754_);
lean_inc(v___x_752_);
lean_inc_ref(v___x_755_);
v___x_756_ = lean_array_push(v___x_755_, v___x_752_);
lean_inc_ref(v___x_756_);
v___x_757_ = lean_array_push(v___x_756_, v___x_753_);
lean_inc_n(v_a_683_, 2);
v___x_758_ = l_Array_append___redArg(v_a_683_, v___x_757_);
lean_dec_ref(v___x_757_);
v___x_759_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v_a_703_);
v___x_760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_760_, 0, v_a_703_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_762_ = l_Lean_Syntax_node1(v_a_703_, v___x_761_, v___x_760_);
v___x_763_ = lean_array_push(v___x_756_, v___x_762_);
v___x_764_ = l_Array_append___redArg(v_a_683_, v___x_763_);
lean_dec_ref(v___x_763_);
v___x_765_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12));
lean_inc_n(v_a_728_, 5);
v___x_766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_766_, 0, v_a_728_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v_sz_767_ = lean_array_size(v___x_764_);
lean_inc_n(v_a_726_, 4);
v___x_768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_768_, 0, v_a_726_);
lean_ctor_set(v___x_768_, 1, v___x_765_);
v_sz_769_ = lean_array_size(v___x_758_);
v___x_770_ = ((size_t)0ULL);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_767_, v___x_770_, v___x_764_);
v___x_772_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14);
v___x_773_ = l_Lean_mkSepArray(v___x_771_, v___x_772_);
lean_dec_ref(v___x_771_);
v___x_774_ = l_Array_append___redArg(v___x_747_, v___x_773_);
lean_dec_ref(v___x_773_);
v___x_775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_775_, 0, v_a_728_);
lean_ctor_set(v___x_775_, 1, v___x_746_);
lean_ctor_set(v___x_775_, 2, v___x_774_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_769_, v___x_770_, v___x_758_);
v___x_777_ = l_Lean_mkSepArray(v___x_776_, v___x_772_);
lean_dec_ref(v___x_776_);
v___x_778_ = l_Array_append___redArg(v___x_747_, v___x_777_);
lean_dec_ref(v___x_777_);
v___x_779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_779_, 0, v_a_726_);
lean_ctor_set(v___x_779_, 1, v___x_746_);
lean_ctor_set(v___x_779_, 2, v___x_778_);
v___x_780_ = l_Lean_Syntax_node1(v_a_728_, v___x_746_, v___x_775_);
v___x_781_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16));
lean_inc_n(v_currMacroScope_699_, 2);
lean_inc_n(v_quotContext_698_, 2);
v___x_782_ = l_Lean_addMacroScope(v_quotContext_698_, v___x_781_, v_currMacroScope_699_);
v___x_783_ = l_Lean_Syntax_node1(v_a_726_, v___x_746_, v___x_779_);
v___x_784_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_785_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_785_, 0, v_a_728_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
lean_inc(v_a_705_);
v___x_786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_786_, 0, v_a_705_);
lean_ctor_set(v___x_786_, 1, v___x_759_);
v___x_787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_787_, 0, v_a_726_);
lean_ctor_set(v___x_787_, 1, v___x_784_);
v___x_788_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20);
v___x_789_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23));
v___x_790_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_790_, 0, v_a_728_);
lean_ctor_set(v___x_790_, 1, v___x_788_);
lean_ctor_set(v___x_790_, 2, v___x_782_);
lean_ctor_set(v___x_790_, 3, v___x_789_);
v___x_791_ = l_Lean_Syntax_node1(v_a_705_, v___x_761_, v___x_786_);
v___x_792_ = lean_array_push(v___x_755_, v___x_791_);
v___x_793_ = lean_array_push(v___x_792_, v___x_752_);
v___x_794_ = l_Array_append___redArg(v_a_683_, v___x_793_);
lean_dec_ref(v___x_793_);
v___x_795_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25));
v___x_796_ = l_Lean_Syntax_node4(v_a_726_, v___x_795_, v___x_768_, v___x_783_, v___x_787_, v_a_724_);
v___x_797_ = l_Lean_Syntax_node4(v_a_728_, v___x_795_, v___x_766_, v___x_780_, v___x_785_, v___x_790_);
lean_inc_n(v_a_730_, 5);
v___x_798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_798_, 0, v_a_730_);
lean_ctor_set(v___x_798_, 1, v___x_765_);
v_sz_799_ = lean_array_size(v___x_794_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_799_, v___x_770_, v___x_794_);
v___x_801_ = l_Lean_mkSepArray(v___x_800_, v___x_772_);
lean_dec_ref(v___x_800_);
v___x_802_ = l_Array_append___redArg(v___x_747_, v___x_801_);
lean_dec_ref(v___x_801_);
v___x_803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_803_, 0, v_a_730_);
lean_ctor_set(v___x_803_, 1, v___x_746_);
lean_ctor_set(v___x_803_, 2, v___x_802_);
v___x_804_ = l_Lean_Syntax_node1(v_a_730_, v___x_746_, v___x_803_);
v___x_805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_805_, 0, v_a_730_);
lean_ctor_set(v___x_805_, 1, v___x_784_);
v___x_806_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27);
v___x_807_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29));
v___x_808_ = l_Lean_addMacroScope(v_quotContext_698_, v___x_807_, v_currMacroScope_699_);
v___x_809_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__33));
v___x_810_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_810_, 0, v_a_730_);
lean_ctor_set(v___x_810_, 1, v___x_806_);
lean_ctor_set(v___x_810_, 2, v___x_808_);
lean_ctor_set(v___x_810_, 3, v___x_809_);
v___x_811_ = l_Lean_Syntax_node4(v_a_730_, v___x_795_, v___x_798_, v___x_804_, v___x_805_, v___x_810_);
v___x_812_ = lean_unsigned_to_nat(3u);
v___x_813_ = lean_mk_empty_array_with_capacity(v___x_812_);
v___x_814_ = lean_array_push(v___x_813_, v___x_796_);
v___x_815_ = lean_array_push(v___x_814_, v___x_797_);
v___x_816_ = lean_array_push(v___x_815_, v___x_811_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_816_);
v___x_818_ = v___x_732_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_a_728_);
lean_dec(v_a_726_);
lean_dec(v_a_724_);
lean_del_object(v___x_716_);
lean_dec(v_fst_713_);
lean_del_object(v___x_711_);
lean_dec(v_fst_709_);
lean_dec(v_a_705_);
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_683_);
lean_dec(v_head_668_);
v_a_823_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_729_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_729_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_a_726_);
lean_dec(v_a_724_);
lean_del_object(v___x_716_);
lean_dec(v_fst_713_);
lean_del_object(v___x_711_);
lean_dec(v_fst_709_);
lean_dec(v_a_705_);
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_683_);
lean_dec(v_head_668_);
lean_dec_ref(v___f_667_);
v_a_831_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_727_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_727_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v_a_724_);
lean_del_object(v___x_716_);
lean_dec(v_fst_713_);
lean_del_object(v___x_711_);
lean_dec(v_fst_709_);
lean_dec(v_a_705_);
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_683_);
lean_dec(v_head_668_);
lean_dec_ref(v___f_667_);
v_a_839_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_725_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_725_);
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
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_del_object(v___x_716_);
lean_dec(v_fst_713_);
lean_del_object(v___x_711_);
lean_dec(v_fst_709_);
lean_dec(v_a_705_);
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_683_);
lean_dec(v_head_668_);
lean_dec_ref(v___f_667_);
v_a_847_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_723_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_723_);
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
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_a_705_);
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_696_);
lean_dec(v_a_683_);
lean_dec(v_head_668_);
lean_dec_ref(v___f_667_);
v_a_858_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_706_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_706_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_696_);
lean_dec(v_a_683_);
lean_dec(v_head_668_);
lean_dec_ref(v___f_667_);
v_a_866_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_704_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_704_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v_a_701_);
lean_dec(v_a_696_);
lean_dec(v_a_683_);
lean_dec(v_head_668_);
lean_dec_ref(v___f_667_);
v_a_874_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_702_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_702_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec(v_a_696_);
lean_dec(v_a_683_);
lean_dec(v_head_668_);
lean_dec_ref(v___f_667_);
v_a_882_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_700_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_700_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec(v_a_683_);
lean_dec(v_head_668_);
lean_dec_ref(v___f_667_);
v_a_890_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_695_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_695_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_a_683_);
lean_dec(v_a_679_);
lean_dec(v_head_668_);
lean_dec_ref(v___f_667_);
lean_dec_ref(v___f_665_);
lean_dec(v___x_663_);
v_a_900_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_685_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_685_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_dec(v_a_679_);
lean_dec(v_head_668_);
lean_dec_ref(v___f_667_);
lean_dec_ref(v___f_665_);
lean_dec_ref(v_alts_664_);
lean_dec(v___x_663_);
return v___x_682_;
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_head_668_);
lean_dec_ref(v___f_667_);
lean_dec_ref(v___f_665_);
lean_dec_ref(v_alts_664_);
lean_dec(v___x_663_);
v_a_908_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_678_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_678_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___boxed(lean_object* v_indVal_916_, lean_object* v___x_917_, lean_object* v_alts_918_, lean_object* v___f_919_, lean_object* v_numFields_920_, lean_object* v___f_921_, lean_object* v_head_922_, lean_object* v_xs_923_, lean_object* v_type_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2(v_indVal_916_, v___x_917_, v_alts_918_, v___f_919_, v_numFields_920_, v___f_921_, v_head_922_, v_xs_923_, v_type_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_xs_923_);
lean_dec(v_numFields_920_);
lean_dec_ref(v_indVal_916_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1(lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_ref_940_; uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_ref_940_ = lean_ctor_get(v___y_937_, 5);
v___x_941_ = 0;
v___x_942_ = l_Lean_SourceInfo_fromRef(v_ref_940_, v___x_941_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1___boxed(lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1(v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0(lean_object* v_rhs_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v_rhs_952_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0___boxed(lean_object* v_rhs_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0(v_rhs_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
return v_res_969_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_instMonadEIO(lean_box(0));
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(lean_object* v_msg_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_toApplicative_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1078_; 
v___x_985_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0);
v___x_986_ = l_StateRefT_x27_instMonad___redArg(v___x_985_);
v_toApplicative_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v___x_986_, 1);
lean_dec(v_unused_1079_);
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_1078_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_toApplicative_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1078_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v_toFunctor_991_; lean_object* v_toSeq_992_; lean_object* v_toSeqLeft_993_; lean_object* v_toSeqRight_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1076_; 
v_toFunctor_991_ = lean_ctor_get(v_toApplicative_987_, 0);
v_toSeq_992_ = lean_ctor_get(v_toApplicative_987_, 2);
v_toSeqLeft_993_ = lean_ctor_get(v_toApplicative_987_, 3);
v_toSeqRight_994_ = lean_ctor_get(v_toApplicative_987_, 4);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_toApplicative_987_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_toApplicative_987_, 1);
lean_dec(v_unused_1077_);
v___x_996_ = v_toApplicative_987_;
v_isShared_997_ = v_isSharedCheck_1076_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_toSeqRight_994_);
lean_inc(v_toSeqLeft_993_);
lean_inc(v_toSeq_992_);
lean_inc(v_toFunctor_991_);
lean_dec(v_toApplicative_987_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1076_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___f_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___x_1007_; 
v___f_998_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__1));
v___f_999_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_991_);
v___f_1000_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1000_, 0, v_toFunctor_991_);
v___f_1001_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1001_, 0, v_toFunctor_991_);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___f_1000_);
lean_ctor_set(v___x_1002_, 1, v___f_1001_);
v___f_1003_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1003_, 0, v_toSeqRight_994_);
v___f_1004_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1004_, 0, v_toSeqLeft_993_);
v___f_1005_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1005_, 0, v_toSeq_992_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 4, v___f_1003_);
lean_ctor_set(v___x_996_, 3, v___f_1004_);
lean_ctor_set(v___x_996_, 2, v___f_1005_);
lean_ctor_set(v___x_996_, 1, v___f_998_);
lean_ctor_set(v___x_996_, 0, v___x_1002_);
v___x_1007_ = v___x_996_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___f_998_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v___f_1005_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v___f_1004_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v___f_1003_);
v___x_1007_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v___f_999_);
lean_ctor_set(v___x_989_, 0, v___x_1007_);
v___x_1009_ = v___x_989_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___f_999_);
v___x_1009_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; lean_object* v_toApplicative_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1072_; 
v___x_1010_ = l_StateRefT_x27_instMonad___redArg(v___x_1009_);
v_toApplicative_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v___x_1010_, 1);
lean_dec(v_unused_1073_);
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1072_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_toApplicative_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1072_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v_toFunctor_1015_; lean_object* v_toSeq_1016_; lean_object* v_toSeqLeft_1017_; lean_object* v_toSeqRight_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1070_; 
v_toFunctor_1015_ = lean_ctor_get(v_toApplicative_1011_, 0);
v_toSeq_1016_ = lean_ctor_get(v_toApplicative_1011_, 2);
v_toSeqLeft_1017_ = lean_ctor_get(v_toApplicative_1011_, 3);
v_toSeqRight_1018_ = lean_ctor_get(v_toApplicative_1011_, 4);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_toApplicative_1011_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v_toApplicative_1011_, 1);
lean_dec(v_unused_1071_);
v___x_1020_ = v_toApplicative_1011_;
v_isShared_1021_ = v_isSharedCheck_1070_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_toSeqRight_1018_);
lean_inc(v_toSeqLeft_1017_);
lean_inc(v_toSeq_1016_);
lean_inc(v_toFunctor_1015_);
lean_dec(v_toApplicative_1011_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1070_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___x_1031_; 
v___f_1022_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__3));
v___f_1023_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1015_);
v___f_1024_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1024_, 0, v_toFunctor_1015_);
v___f_1025_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1025_, 0, v_toFunctor_1015_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___f_1024_);
lean_ctor_set(v___x_1026_, 1, v___f_1025_);
v___f_1027_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1027_, 0, v_toSeqRight_1018_);
v___f_1028_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1028_, 0, v_toSeqLeft_1017_);
v___f_1029_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1029_, 0, v_toSeq_1016_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 4, v___f_1027_);
lean_ctor_set(v___x_1020_, 3, v___f_1028_);
lean_ctor_set(v___x_1020_, 2, v___f_1029_);
lean_ctor_set(v___x_1020_, 1, v___f_1022_);
lean_ctor_set(v___x_1020_, 0, v___x_1026_);
v___x_1031_ = v___x_1020_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___f_1022_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v___f_1029_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v___f_1028_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v___f_1027_);
v___x_1031_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1033_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v___f_1023_);
lean_ctor_set(v___x_1013_, 0, v___x_1031_);
v___x_1033_ = v___x_1013_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___f_1023_);
v___x_1033_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; lean_object* v_toApplicative_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1066_; 
v___x_1034_ = l_StateRefT_x27_instMonad___redArg(v___x_1033_);
v_toApplicative_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v___x_1034_, 1);
lean_dec(v_unused_1067_);
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1066_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_toApplicative_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1066_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v_toFunctor_1039_; lean_object* v_toSeq_1040_; lean_object* v_toSeqLeft_1041_; lean_object* v_toSeqRight_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1064_; 
v_toFunctor_1039_ = lean_ctor_get(v_toApplicative_1035_, 0);
v_toSeq_1040_ = lean_ctor_get(v_toApplicative_1035_, 2);
v_toSeqLeft_1041_ = lean_ctor_get(v_toApplicative_1035_, 3);
v_toSeqRight_1042_ = lean_ctor_get(v_toApplicative_1035_, 4);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_toApplicative_1035_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_toApplicative_1035_, 1);
lean_dec(v_unused_1065_);
v___x_1044_ = v_toApplicative_1035_;
v_isShared_1045_ = v_isSharedCheck_1064_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_toSeqRight_1042_);
lean_inc(v_toSeqLeft_1041_);
lean_inc(v_toSeq_1040_);
lean_inc(v_toFunctor_1039_);
lean_dec(v_toApplicative_1035_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1064_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___x_1050_; lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___x_1055_; 
v___f_1046_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__5));
v___f_1047_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1039_);
v___f_1048_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1048_, 0, v_toFunctor_1039_);
v___f_1049_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1049_, 0, v_toFunctor_1039_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___f_1048_);
lean_ctor_set(v___x_1050_, 1, v___f_1049_);
v___f_1051_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1051_, 0, v_toSeqRight_1042_);
v___f_1052_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1052_, 0, v_toSeqLeft_1041_);
v___f_1053_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1053_, 0, v_toSeq_1040_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 4, v___f_1051_);
lean_ctor_set(v___x_1044_, 3, v___f_1052_);
lean_ctor_set(v___x_1044_, 2, v___f_1053_);
lean_ctor_set(v___x_1044_, 1, v___f_1046_);
lean_ctor_set(v___x_1044_, 0, v___x_1050_);
v___x_1055_ = v___x_1044_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___f_1046_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v___f_1053_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v___f_1052_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v___f_1051_);
v___x_1055_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___f_1047_);
lean_ctor_set(v___x_1037_, 0, v___x_1055_);
v___x_1057_ = v___x_1037_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___f_1047_);
v___x_1057_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_47034__overap_1060_; lean_object* v___x_1061_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = l_instInhabitedOfMonad___redArg(v___x_1057_, v___x_1058_);
v___x_47034__overap_1060_ = lean_panic_fn_borrowed(v___x_1059_, v_msg_977_);
lean_dec(v___x_1059_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
v___x_1061_ = lean_apply_7(v___x_47034__overap_1060_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, lean_box(0));
return v___x_1061_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(v_msg_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v_env_1096_; lean_object* v___x_1097_; lean_object* v_mctx_1098_; lean_object* v_lctx_1099_; lean_object* v_options_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1095_ = lean_st_ref_get(v___y_1093_);
v_env_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_ref(v_env_1096_);
lean_dec(v___x_1095_);
v___x_1097_ = lean_st_ref_get(v___y_1091_);
v_mctx_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_mctx_1098_);
lean_dec(v___x_1097_);
v_lctx_1099_ = lean_ctor_get(v___y_1090_, 2);
v_options_1100_ = lean_ctor_get(v___y_1092_, 2);
lean_inc_ref(v_options_1100_);
lean_inc_ref(v_lctx_1099_);
v___x_1101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1101_, 0, v_env_1096_);
lean_ctor_set(v___x_1101_, 1, v_mctx_1098_);
lean_ctor_set(v___x_1101_, 2, v_lctx_1099_);
lean_ctor_set(v___x_1101_, 3, v_options_1100_);
v___x_1102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v_msgData_1089_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msgData_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1110_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_box(1);
v___x_1112_ = l_Lean_MessageData_ofFormat(v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2));
v___x_1117_ = l_Lean_MessageData_ofFormat(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
if (lean_obj_tag(v_x_1119_) == 0)
{
return v_x_1118_;
}
else
{
lean_object* v_head_1120_; lean_object* v_tail_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1143_; 
v_head_1120_ = lean_ctor_get(v_x_1119_, 0);
v_tail_1121_ = lean_ctor_get(v_x_1119_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_x_1119_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1123_ = v_x_1119_;
v_isShared_1124_ = v_isSharedCheck_1143_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_tail_1121_);
lean_inc(v_head_1120_);
lean_dec(v_x_1119_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1143_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_before_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1141_; 
v_before_1125_ = lean_ctor_get(v_head_1120_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_head_1120_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v_head_1120_, 1);
lean_dec(v_unused_1142_);
v___x_1127_ = v_head_1120_;
v_isShared_1128_ = v_isSharedCheck_1141_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_before_1125_);
lean_dec(v_head_1120_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1141_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_1128_ == 0)
{
lean_ctor_set_tag(v___x_1127_, 7);
lean_ctor_set(v___x_1127_, 1, v___x_1129_);
lean_ctor_set(v___x_1127_, 0, v_x_1118_);
v___x_1131_ = v___x_1127_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_x_1118_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3);
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 7);
lean_ctor_set(v___x_1123_, 1, v___x_1132_);
lean_ctor_set(v___x_1123_, 0, v___x_1131_);
v___x_1134_ = v___x_1123_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = l_Lean_MessageData_ofSyntax(v_before_1125_);
v___x_1136_ = l_Lean_indentD(v___x_1135_);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1134_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v_x_1118_ = v___x_1137_;
v_x_1119_ = v_tail_1121_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_opts_1144_, lean_object* v_opt_1145_){
_start:
{
lean_object* v_name_1146_; lean_object* v_defValue_1147_; lean_object* v_map_1148_; lean_object* v___x_1149_; 
v_name_1146_ = lean_ctor_get(v_opt_1145_, 0);
v_defValue_1147_ = lean_ctor_get(v_opt_1145_, 1);
v_map_1148_ = lean_ctor_get(v_opts_1144_, 0);
v___x_1149_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1148_, v_name_1146_);
if (lean_obj_tag(v___x_1149_) == 0)
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_unbox(v_defValue_1147_);
return v___x_1150_;
}
else
{
lean_object* v_val_1151_; 
v_val_1151_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_val_1151_);
lean_dec_ref_known(v___x_1149_, 1);
if (lean_obj_tag(v_val_1151_) == 1)
{
uint8_t v_v_1152_; 
v_v_1152_ = lean_ctor_get_uint8(v_val_1151_, 0);
lean_dec_ref_known(v_val_1151_, 0);
return v_v_1152_;
}
else
{
uint8_t v___x_1153_; 
lean_dec(v_val_1151_);
v___x_1153_ = lean_unbox(v_defValue_1147_);
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_opts_1154_, lean_object* v_opt_1155_){
_start:
{
uint8_t v_res_1156_; lean_object* v_r_1157_; 
v_res_1156_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_1154_, v_opt_1155_);
lean_dec_ref(v_opt_1155_);
lean_dec_ref(v_opts_1154_);
v_r_1157_ = lean_box(v_res_1156_);
return v_r_1157_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_1162_ = l_Lean_MessageData_ofFormat(v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_1163_, lean_object* v_macroStack_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_options_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; uint8_t v___x_1170_; 
v_options_1167_ = lean_ctor_get(v___y_1165_, 2);
v___x_1168_ = l_Lean_Elab_pp_macroStack;
v___x_1169_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_options_1167_, v___x_1168_);
v___x_1170_ = lean_bool_not(v___x_1169_);
if (v___x_1170_ == 0)
{
if (lean_obj_tag(v_macroStack_1164_) == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_msgData_1163_);
return v___x_1171_;
}
else
{
lean_object* v_head_1172_; lean_object* v_after_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1188_; 
v_head_1172_ = lean_ctor_get(v_macroStack_1164_, 0);
lean_inc(v_head_1172_);
v_after_1173_ = lean_ctor_get(v_head_1172_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_head_1172_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v_head_1172_, 0);
lean_dec(v_unused_1189_);
v___x_1175_ = v_head_1172_;
v_isShared_1176_ = v_isSharedCheck_1188_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_after_1173_);
lean_dec(v_head_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1188_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_1176_ == 0)
{
lean_ctor_set_tag(v___x_1175_, 7);
lean_ctor_set(v___x_1175_, 1, v___x_1177_);
lean_ctor_set(v___x_1175_, 0, v_msgData_1163_);
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_msgData_1163_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_msgData_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1180_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = l_Lean_MessageData_ofSyntax(v_after_1173_);
v___x_1183_ = l_Lean_indentD(v___x_1182_);
v_msgData_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1184_, 0, v___x_1181_);
lean_ctor_set(v_msgData_1184_, 1, v___x_1183_);
v___x_1185_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(v_msgData_1184_, v_macroStack_1164_);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
}
}
else
{
lean_object* v___x_1190_; 
lean_dec(v_macroStack_1164_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_msgData_1163_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_1191_, lean_object* v_macroStack_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1191_, v_macroStack_1192_, v___y_1193_);
lean_dec_ref(v___y_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_ref_1204_; lean_object* v___x_1205_; lean_object* v_a_1206_; lean_object* v_macroStack_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1218_; 
v_ref_1204_ = lean_ctor_get(v___y_1201_, 5);
v___x_1205_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_1196_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref(v___x_1205_);
v_macroStack_1207_ = lean_ctor_get(v___y_1197_, 1);
v___x_1208_ = l_Lean_Elab_getBetterRef(v_ref_1204_, v_macroStack_1207_);
lean_inc(v_macroStack_1207_);
v___x_1209_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_1206_, v_macroStack_1207_, v___y_1201_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1208_);
lean_ctor_set(v___x_1214_, 1, v_a_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set_tag(v___x_1212_, 1);
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1227_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__0));
v___x_1230_ = l_Lean_stringToMessageData(v___x_1229_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__2));
v___x_1233_ = l_Lean_stringToMessageData(v___x_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1237_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__6));
v___x_1238_ = lean_unsigned_to_nat(11u);
v___x_1239_ = lean_unsigned_to_nat(122u);
v___x_1240_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__5));
v___x_1241_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__4));
v___x_1242_ = l_mkPanicMessageWithDecl(v___x_1241_, v___x_1240_, v___x_1239_, v___x_1238_, v___x_1237_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(lean_object* v_constName_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1259_; lean_object* v_env_1260_; uint8_t v___x_1261_; lean_object* v___x_1262_; 
v___x_1259_ = lean_st_ref_get(v___y_1249_);
v_env_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc_ref(v_env_1260_);
lean_dec(v___x_1259_);
v___x_1261_ = 0;
lean_inc(v_constName_1243_);
v___x_1262_ = l_Lean_Environment_findAsync_x3f(v_env_1260_, v_constName_1243_, v___x_1261_);
if (lean_obj_tag(v___x_1262_) == 1)
{
lean_object* v_val_1263_; uint8_t v_kind_1264_; 
v_val_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_val_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v_kind_1264_ = lean_ctor_get_uint8(v_val_1263_, sizeof(void*)*3);
if (v_kind_1264_ == 6)
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1263_);
if (lean_obj_tag(v___x_1265_) == 6)
{
lean_object* v_val_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_constName_1243_);
v_val_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_val_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 0);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_val_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_dec_ref(v___x_1265_);
v___x_1274_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7);
v___x_1275_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(v___x_1274_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1284_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1284_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1284_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
if (lean_obj_tag(v_a_1276_) == 0)
{
lean_del_object(v___x_1278_);
goto v___jp_1251_;
}
else
{
lean_object* v_val_1280_; lean_object* v___x_1282_; 
lean_dec(v_constName_1243_);
v_val_1280_ = lean_ctor_get(v_a_1276_, 0);
lean_inc(v_val_1280_);
lean_dec_ref_known(v_a_1276_, 1);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v_val_1280_);
v___x_1282_ = v___x_1278_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_val_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_constName_1243_);
v_a_1285_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1275_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1275_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
else
{
lean_dec(v_val_1263_);
goto v___jp_1251_;
}
}
else
{
lean_dec(v___x_1262_);
goto v___jp_1251_;
}
v___jp_1251_:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1252_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_1253_ = 0;
v___x_1254_ = l_Lean_MessageData_ofConstName(v_constName_1243_, v___x_1253_);
v___x_1255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1252_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v___x_1257_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___boxed(lean_object* v_constName_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v_constName_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(size_t v_sz_1302_, size_t v_i_1303_, lean_object* v_bs_1304_){
_start:
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_usize_dec_lt(v_i_1303_, v_sz_1302_);
if (v___x_1305_ == 0)
{
return v_bs_1304_;
}
else
{
lean_object* v_v_1306_; lean_object* v___x_1307_; lean_object* v_bs_x27_1308_; size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v_v_1306_ = lean_array_uget(v_bs_1304_, v_i_1303_);
v___x_1307_ = lean_unsigned_to_nat(0u);
v_bs_x27_1308_ = lean_array_uset(v_bs_1304_, v_i_1303_, v___x_1307_);
v___x_1309_ = ((size_t)1ULL);
v___x_1310_ = lean_usize_add(v_i_1303_, v___x_1309_);
v___x_1311_ = lean_array_uset(v_bs_x27_1308_, v_i_1303_, v_v_1306_);
v_i_1303_ = v___x_1310_;
v_bs_1304_ = v___x_1311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6___boxed(lean_object* v_sz_1313_, lean_object* v_i_1314_, lean_object* v_bs_1315_){
_start:
{
size_t v_sz_boxed_1316_; size_t v_i_boxed_1317_; lean_object* v_res_1318_; 
v_sz_boxed_1316_ = lean_unbox_usize(v_sz_1313_);
lean_dec(v_sz_1313_);
v_i_boxed_1317_ = lean_unbox_usize(v_i_1314_);
lean_dec(v_i_1314_);
v_res_1318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(v_sz_boxed_1316_, v_i_boxed_1317_, v_bs_1315_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(lean_object* v_indVal_1323_, lean_object* v_as_x27_1324_, lean_object* v_b_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
if (lean_obj_tag(v_as_x27_1324_) == 0)
{
lean_object* v___x_1333_; 
lean_dec_ref(v_indVal_1323_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v_b_1325_);
return v___x_1333_;
}
else
{
lean_object* v_head_1334_; lean_object* v_tail_1335_; lean_object* v___x_1336_; 
v_head_1334_ = lean_ctor_get(v_as_x27_1324_, 0);
v_tail_1335_ = lean_ctor_get(v_as_x27_1324_, 1);
lean_inc(v_head_1334_);
v___x_1336_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v_head_1334_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v_toConstantVal_1338_; lean_object* v_numFields_1339_; lean_object* v_type_1340_; lean_object* v___f_1341_; lean_object* v___f_1342_; lean_object* v___x_1343_; lean_object* v_alts_1344_; lean_object* v___f_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v_toConstantVal_1338_ = lean_ctor_get(v_a_1337_, 0);
lean_inc_ref(v_toConstantVal_1338_);
v_numFields_1339_ = lean_ctor_get(v_a_1337_, 4);
lean_inc(v_numFields_1339_);
lean_dec(v_a_1337_);
v_type_1340_ = lean_ctor_get(v_toConstantVal_1338_, 2);
lean_inc_ref(v_type_1340_);
lean_dec_ref(v_toConstantVal_1338_);
v___f_1341_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0));
v___f_1342_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1));
v___x_1343_ = lean_unsigned_to_nat(0u);
v_alts_1344_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
lean_inc(v_head_1334_);
lean_inc_ref(v_indVal_1323_);
v___f_1345_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___boxed), 16, 7);
lean_closure_set(v___f_1345_, 0, v_indVal_1323_);
lean_closure_set(v___f_1345_, 1, v___x_1343_);
lean_closure_set(v___f_1345_, 2, v_alts_1344_);
lean_closure_set(v___f_1345_, 3, v___f_1341_);
lean_closure_set(v___f_1345_, 4, v_numFields_1339_);
lean_closure_set(v___f_1345_, 5, v___f_1342_);
lean_closure_set(v___f_1345_, 6, v_head_1334_);
v___x_1346_ = 0;
v___x_1347_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_1340_, v___f_1345_, v___x_1346_, v___x_1346_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; size_t v_sz_1349_; size_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v_sz_1349_ = lean_array_size(v_a_1348_);
v___x_1350_ = ((size_t)0ULL);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(v_sz_1349_, v___x_1350_, v_a_1348_);
v___x_1352_ = l_Array_append___redArg(v_b_1325_, v___x_1351_);
lean_dec_ref(v___x_1351_);
v_as_x27_1324_ = v_tail_1335_;
v_b_1325_ = v___x_1352_;
goto _start;
}
else
{
lean_dec_ref(v_b_1325_);
lean_dec_ref(v_indVal_1323_);
return v___x_1347_;
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_b_1325_);
lean_dec_ref(v_indVal_1323_);
v_a_1354_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1336_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1336_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___boxed(lean_object* v_indVal_1362_, lean_object* v_as_x27_1363_, lean_object* v_b_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1362_, v_as_x27_1363_, v_b_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v_as_x27_1363_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(lean_object* v_indVal_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_ctors_1381_; lean_object* v_alts_1382_; lean_object* v___x_1383_; 
v_ctors_1381_ = lean_ctor_get(v_indVal_1373_, 4);
lean_inc(v_ctors_1381_);
v_alts_1382_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_1383_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1373_, v_ctors_1381_, v_alts_1382_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_);
lean_dec(v_ctors_1381_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1393_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1388_ = lean_array_pop(v_a_1384_);
v___x_1389_ = lean_array_pop(v___x_1388_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1389_);
v___x_1391_ = v___x_1386_;
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
}
else
{
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts___boxed(lean_object* v_indVal_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(v_indVal_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2(lean_object* v_upperBound_1403_, lean_object* v___x_1404_, lean_object* v_xs_1405_, lean_object* v_a_1406_, lean_object* v_inst_1407_, lean_object* v_R_1408_, lean_object* v_a_1409_, lean_object* v_b_1410_, lean_object* v_c_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(v_upperBound_1403_, v___x_1404_, v_xs_1405_, v_a_1406_, v_a_1409_, v_b_1410_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___boxed(lean_object* v_upperBound_1420_, lean_object* v___x_1421_, lean_object* v_xs_1422_, lean_object* v_a_1423_, lean_object* v_inst_1424_, lean_object* v_R_1425_, lean_object* v_a_1426_, lean_object* v_b_1427_, lean_object* v_c_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2(v_upperBound_1420_, v___x_1421_, v_xs_1422_, v_a_1423_, v_inst_1424_, v_R_1425_, v_a_1426_, v_b_1427_, v_c_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec_ref(v_a_1423_);
lean_dec_ref(v_xs_1422_);
lean_dec(v___x_1421_);
lean_dec(v_upperBound_1420_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3(lean_object* v_upperBound_1437_, lean_object* v_inst_1438_, lean_object* v_R_1439_, lean_object* v_a_1440_, lean_object* v_b_1441_, lean_object* v_c_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_1437_, v_a_1440_, v_b_1441_, v___y_1447_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___boxed(lean_object* v_upperBound_1451_, lean_object* v_inst_1452_, lean_object* v_R_1453_, lean_object* v_a_1454_, lean_object* v_b_1455_, lean_object* v_c_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3(v_upperBound_1451_, v_inst_1452_, v_R_1453_, v_a_1454_, v_b_1455_, v_c_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v_upperBound_1451_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4(lean_object* v_upperBound_1465_, lean_object* v_inst_1466_, lean_object* v_R_1467_, lean_object* v_a_1468_, lean_object* v_b_1469_, lean_object* v_c_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(v_upperBound_1465_, v_a_1468_, v_b_1469_, v___y_1475_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___boxed(lean_object* v_upperBound_1479_, lean_object* v_inst_1480_, lean_object* v_R_1481_, lean_object* v_a_1482_, lean_object* v_b_1483_, lean_object* v_c_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4(v_upperBound_1479_, v_inst_1480_, v_R_1481_, v_a_1482_, v_b_1483_, v_c_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v_upperBound_1479_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7(lean_object* v_indVal_1493_, lean_object* v_as_1494_, lean_object* v_as_x27_1495_, lean_object* v_b_1496_, lean_object* v_a_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1493_, v_as_x27_1495_, v_b_1496_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___boxed(lean_object* v_indVal_1506_, lean_object* v_as_1507_, lean_object* v_as_x27_1508_, lean_object* v_b_1509_, lean_object* v_a_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7(v_indVal_1506_, v_as_1507_, v_as_x27_1508_, v_b_1509_, v_a_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v_as_x27_1508_);
lean_dec(v_as_1507_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1519_, lean_object* v_msg_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1529_, lean_object* v_msg_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0(v_00_u03b1_1529_, v_msg_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1539_, lean_object* v_macroStack_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1539_, v_macroStack_1540_, v___y_1545_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1549_, lean_object* v_macroStack_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(v_msgData_1549_, v_macroStack_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(lean_object* v_header_1572_, lean_object* v_indVal_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; 
lean_inc_ref(v_indVal_1573_);
v___x_1581_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_1572_, v_indVal_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(v_indVal_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1614_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1614_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1614_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v_ref_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; size_t v_sz_1597_; size_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v_ref_1588_ = lean_ctor_get(v_a_1578_, 5);
v___x_1589_ = 0;
v___x_1590_ = l_Lean_SourceInfo_fromRef(v_ref_1588_, v___x_1589_);
v___x_1591_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0));
v___x_1592_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1));
lean_inc_n(v___x_1590_, 6);
v___x_1593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1590_);
lean_ctor_set(v___x_1593_, 1, v___x_1591_);
v___x_1594_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1595_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_1596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1590_);
lean_ctor_set(v___x_1596_, 1, v___x_1594_);
lean_ctor_set(v___x_1596_, 2, v___x_1595_);
v_sz_1597_ = lean_array_size(v_a_1582_);
v___x_1598_ = ((size_t)0ULL);
v___x_1599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_1597_, v___x_1598_, v_a_1582_);
v___x_1600_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14);
v___x_1601_ = l_Lean_mkSepArray(v___x_1599_, v___x_1600_);
lean_dec_ref(v___x_1599_);
v___x_1602_ = l_Array_append___redArg(v___x_1595_, v___x_1601_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1590_);
lean_ctor_set(v___x_1603_, 1, v___x_1594_);
lean_ctor_set(v___x_1603_, 2, v___x_1602_);
v___x_1604_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2));
v___x_1605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1590_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4));
v___x_1607_ = l_Array_append___redArg(v___x_1595_, v_a_1584_);
lean_dec(v_a_1584_);
v___x_1608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1590_);
lean_ctor_set(v___x_1608_, 1, v___x_1594_);
lean_ctor_set(v___x_1608_, 2, v___x_1607_);
v___x_1609_ = l_Lean_Syntax_node1(v___x_1590_, v___x_1606_, v___x_1608_);
lean_inc_ref(v___x_1596_);
v___x_1610_ = l_Lean_Syntax_node6(v___x_1590_, v___x_1592_, v___x_1593_, v___x_1596_, v___x_1596_, v___x_1603_, v___x_1605_, v___x_1609_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1610_);
v___x_1612_ = v___x_1586_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_a_1582_);
v_a_1615_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1583_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1583_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v_indVal_1573_);
v_a_1623_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1581_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1581_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___boxed(lean_object* v_header_1631_, lean_object* v_indVal_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(v_header_1631_, v_indVal_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
return v_res_1640_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0(lean_object* v_msg_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_27926__overap_1651_; lean_object* v___x_1652_; 
v___x_1650_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___closed__0);
v___x_27926__overap_1651_ = lean_panic_fn_borrowed(v___x_1650_, v_msg_1642_);
lean_inc(v___y_1648_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
lean_inc(v___y_1644_);
lean_inc_ref(v___y_1643_);
v___x_1652_ = lean_apply_7(v___x_27926__overap_1651_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, lean_box(0));
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___boxed(lean_object* v_msg_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0(v_msg_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___lam__0(uint8_t v_a_1662_, lean_object* v___x_1663_, lean_object* v___x_1664_, lean_object* v_snd_1665_, lean_object* v_rhs_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_ref_1674_; lean_object* v_quotContext_1675_; lean_object* v_currMacroScope_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_ref_1674_ = lean_ctor_get(v___y_1671_, 5);
v_quotContext_1675_ = lean_ctor_get(v___y_1671_, 10);
v_currMacroScope_1676_ = lean_ctor_get(v___y_1671_, 11);
v___x_1677_ = l_Lean_SourceInfo_fromRef(v_ref_1674_, v_a_1662_);
v___x_1678_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_1679_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5);
v___x_1680_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8));
lean_inc_n(v_currMacroScope_1676_, 3);
lean_inc_n(v_quotContext_1675_, 3);
v___x_1681_ = l_Lean_addMacroScope(v_quotContext_1675_, v___x_1680_, v_currMacroScope_1676_);
v___x_1682_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12));
lean_inc_n(v___x_1677_, 11);
v___x_1683_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1677_);
lean_ctor_set(v___x_1683_, 1, v___x_1679_);
lean_ctor_set(v___x_1683_, 2, v___x_1681_);
lean_ctor_set(v___x_1683_, 3, v___x_1682_);
v___x_1684_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1685_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16));
v___x_1686_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_1687_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_1688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1677_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_1690_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_1691_ = lean_box(0);
v___x_1692_ = l_Lean_addMacroScope(v_quotContext_1675_, v___x_1691_, v_currMacroScope_1676_);
v___x_1693_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33));
v___x_1694_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1677_);
lean_ctor_set(v___x_1694_, 1, v___x_1690_);
lean_ctor_set(v___x_1694_, 2, v___x_1692_);
lean_ctor_set(v___x_1694_, 3, v___x_1693_);
v___x_1695_ = l_Lean_Syntax_node1(v___x_1677_, v___x_1689_, v___x_1694_);
v___x_1696_ = l_Lean_Syntax_node2(v___x_1677_, v___x_1686_, v___x_1688_, v___x_1695_);
v___x_1697_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_1698_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
v___x_1699_ = l_Lean_addMacroScope(v_quotContext_1675_, v___x_1698_, v_currMacroScope_1676_);
v___x_1700_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39));
v___x_1701_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1677_);
lean_ctor_set(v___x_1701_, 1, v___x_1697_);
lean_ctor_set(v___x_1701_, 2, v___x_1699_);
lean_ctor_set(v___x_1701_, 3, v___x_1700_);
v___x_1702_ = l_Lean_Syntax_node2(v___x_1677_, v___x_1684_, v___x_1663_, v___x_1664_);
v___x_1703_ = l_Lean_Syntax_node2(v___x_1677_, v___x_1678_, v___x_1701_, v___x_1702_);
v___x_1704_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_1705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1677_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = l_Lean_Syntax_node3(v___x_1677_, v___x_1685_, v___x_1696_, v___x_1703_, v___x_1705_);
v___x_1707_ = l_Lean_Syntax_node2(v___x_1677_, v___x_1684_, v___x_1706_, v_rhs_1666_);
v___x_1708_ = l_Lean_Syntax_node2(v___x_1677_, v___x_1678_, v___x_1683_, v___x_1707_);
lean_inc(v___y_1672_);
lean_inc_ref(v___y_1671_);
lean_inc(v___y_1670_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
v___x_1709_ = lean_apply_8(v_snd_1665_, v___x_1708_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, lean_box(0));
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___lam__0___boxed(lean_object* v_a_1710_, lean_object* v___x_1711_, lean_object* v___x_1712_, lean_object* v_snd_1713_, lean_object* v_rhs_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v_a_29384__boxed_1722_; lean_object* v_res_1723_; 
v_a_29384__boxed_1722_ = lean_unbox(v_a_1710_);
v_res_1723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___lam__0(v_a_29384__boxed_1722_, v___x_1711_, v___x_1712_, v_snd_1713_, v_rhs_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg(lean_object* v_upperBound_1725_, lean_object* v_indVal_1726_, lean_object* v_xs_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_a_1737_; uint8_t v___x_1741_; 
v___x_1741_ = lean_nat_dec_lt(v_a_1729_, v_upperBound_1725_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; 
lean_dec(v_a_1729_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_b_1730_);
return v___x_1742_;
}
else
{
lean_object* v_snd_1743_; lean_object* v_fst_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1845_; 
v_snd_1743_ = lean_ctor_get(v_b_1730_, 1);
v_fst_1744_ = lean_ctor_get(v_b_1730_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_b_1730_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1746_ = v_b_1730_;
v_isShared_1747_ = v_isSharedCheck_1845_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_snd_1743_);
lean_inc(v_fst_1744_);
lean_dec(v_b_1730_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1845_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v_fst_1748_; lean_object* v_snd_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1844_; 
v_fst_1748_ = lean_ctor_get(v_snd_1743_, 0);
v_snd_1749_ = lean_ctor_get(v_snd_1743_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_snd_1743_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1751_ = v_snd_1743_;
v_isShared_1752_ = v_isSharedCheck_1844_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_snd_1749_);
lean_inc(v_fst_1748_);
lean_dec(v_snd_1743_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1844_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_numParams_1753_; lean_object* v_lctx_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_numParams_1753_ = lean_ctor_get(v_indVal_1726_, 1);
v_lctx_1754_ = lean_ctor_get(v___y_1731_, 2);
v___x_1755_ = l_Lean_instInhabitedExpr;
v___x_1756_ = lean_nat_add(v_numParams_1753_, v_a_1729_);
v___x_1757_ = lean_array_get_borrowed(v___x_1755_, v_xs_1727_, v___x_1756_);
lean_dec(v___x_1756_);
lean_inc(v___x_1757_);
lean_inc_ref(v_lctx_1754_);
v___x_1758_ = l_Lean_Meta_occursOrInType(v_lctx_1754_, v___x_1757_, v_a_1728_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = l_Lean_Expr_fvarId_x21(v___x_1757_);
v___x_1760_ = l_Lean_FVarId_getUserName___redArg(v___x_1759_, v___y_1731_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1762_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc_n(v_a_1761_, 2);
lean_dec_ref_known(v___x_1760_, 1);
v___x_1762_ = l_Lean_Core_mkFreshUserName(v_a_1761_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___closed__0));
v___x_1765_ = lean_name_append_after(v_a_1761_, v___x_1764_);
v___x_1766_ = l_Lean_Core_mkFreshUserName(v___x_1765_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v___x_1757_);
v___x_1768_ = lean_infer_type(v___x_1757_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1770_ = l_Lean_Meta_isProp(v_a_1769_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = l_Lean_mkIdent(v_a_1763_);
v___x_1773_ = l_Lean_mkIdent(v_a_1767_);
lean_inc(v___x_1772_);
v___x_1774_ = lean_array_push(v_fst_1744_, v___x_1772_);
lean_inc(v___x_1773_);
v___x_1775_ = lean_array_push(v_fst_1748_, v___x_1773_);
v___x_1776_ = lean_unbox(v_a_1771_);
if (v___x_1776_ == 0)
{
lean_object* v___f_1777_; lean_object* v___x_1779_; 
v___f_1777_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_1777_, 0, v_a_1771_);
lean_closure_set(v___f_1777_, 1, v___x_1772_);
lean_closure_set(v___f_1777_, 2, v___x_1773_);
lean_closure_set(v___f_1777_, 3, v_snd_1749_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 1, v___f_1777_);
lean_ctor_set(v___x_1751_, 0, v___x_1775_);
v___x_1779_ = v___x_1751_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v___f_1777_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v___x_1779_);
lean_ctor_set(v___x_1746_, 0, v___x_1774_);
v___x_1781_ = v___x_1746_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
v_a_1737_ = v___x_1781_;
goto v___jp_1736_;
}
}
}
else
{
lean_object* v___x_1785_; 
lean_dec(v___x_1773_);
lean_dec(v___x_1772_);
lean_dec(v_a_1771_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1775_);
v___x_1785_ = v___x_1751_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_snd_1749_);
v___x_1785_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1787_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v___x_1785_);
lean_ctor_set(v___x_1746_, 0, v___x_1774_);
v___x_1787_ = v___x_1746_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
v_a_1737_ = v___x_1787_;
goto v___jp_1736_;
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec(v_a_1767_);
lean_dec(v_a_1763_);
lean_del_object(v___x_1751_);
lean_dec(v_snd_1749_);
lean_dec(v_fst_1748_);
lean_del_object(v___x_1746_);
lean_dec(v_fst_1744_);
lean_dec(v_a_1729_);
v_a_1790_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1770_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1770_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_a_1767_);
lean_dec(v_a_1763_);
lean_del_object(v___x_1751_);
lean_dec(v_snd_1749_);
lean_dec(v_fst_1748_);
lean_del_object(v___x_1746_);
lean_dec(v_fst_1744_);
lean_dec(v_a_1729_);
v_a_1798_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1768_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1768_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_a_1763_);
lean_del_object(v___x_1751_);
lean_dec(v_snd_1749_);
lean_dec(v_fst_1748_);
lean_del_object(v___x_1746_);
lean_dec(v_fst_1744_);
lean_dec(v_a_1729_);
v_a_1806_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1766_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1766_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec(v_a_1761_);
lean_del_object(v___x_1751_);
lean_dec(v_snd_1749_);
lean_dec(v_fst_1748_);
lean_del_object(v___x_1746_);
lean_dec(v_fst_1744_);
lean_dec(v_a_1729_);
v_a_1814_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1762_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1762_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_del_object(v___x_1751_);
lean_dec(v_snd_1749_);
lean_dec(v_fst_1748_);
lean_del_object(v___x_1746_);
lean_dec(v_fst_1744_);
lean_dec(v_a_1729_);
v_a_1822_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1760_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1760_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_ref_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v_ref_1830_ = lean_ctor_get(v___y_1733_, 5);
v___x_1831_ = 0;
v___x_1832_ = l_Lean_SourceInfo_fromRef(v_ref_1830_, v___x_1831_);
v___x_1833_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_1834_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_1832_);
v___x_1835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1832_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Lean_Syntax_node1(v___x_1832_, v___x_1833_, v___x_1835_);
v___x_1837_ = lean_array_push(v_fst_1744_, v___x_1836_);
if (v_isShared_1752_ == 0)
{
v___x_1839_ = v___x_1751_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_fst_1748_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_snd_1749_);
v___x_1839_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v___x_1839_);
lean_ctor_set(v___x_1746_, 0, v___x_1837_);
v___x_1841_ = v___x_1746_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
v_a_1737_ = v___x_1841_;
goto v___jp_1736_;
}
}
}
}
}
}
v___jp_1736_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_a_1729_, v___x_1738_);
lean_dec(v_a_1729_);
v_a_1729_ = v___x_1739_;
v_b_1730_ = v_a_1737_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg___boxed(lean_object* v_upperBound_1846_, lean_object* v_indVal_1847_, lean_object* v_xs_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_b_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg(v_upperBound_1846_, v_indVal_1847_, v_xs_1848_, v_a_1849_, v_a_1850_, v_b_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec_ref(v_a_1849_);
lean_dec_ref(v_xs_1848_);
lean_dec_ref(v_indVal_1847_);
lean_dec(v_upperBound_1846_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2(lean_object* v___f_1876_, lean_object* v_numFields_1877_, lean_object* v_indVal_1878_, lean_object* v___f_1879_, lean_object* v_xs_1880_, lean_object* v_type_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_Core_betaReduce(v_type_1881_, v___y_1886_, v___y_1887_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v___x_1889_, 1);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___f_1876_);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg(v_numFields_1877_, v_indVal_1878_, v_xs_1880_, v_a_1890_, v___x_1891_, v___x_1894_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
lean_dec(v_a_1890_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v_snd_1897_; lean_object* v_fst_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1998_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v_snd_1897_ = lean_ctor_get(v_a_1896_, 1);
v_fst_1898_ = lean_ctor_get(v_a_1896_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_a_1896_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1900_ = v_a_1896_;
v_isShared_1901_ = v_isSharedCheck_1998_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_snd_1897_);
lean_inc(v_fst_1898_);
lean_dec(v_a_1896_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1998_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v_fst_1902_; lean_object* v_snd_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1997_; 
v_fst_1902_ = lean_ctor_get(v_snd_1897_, 0);
v_snd_1903_ = lean_ctor_get(v_snd_1897_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_snd_1897_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1905_ = v_snd_1897_;
v_isShared_1906_ = v_isSharedCheck_1997_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_snd_1903_);
lean_inc(v_fst_1902_);
lean_dec(v_snd_1897_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1997_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v_ref_1907_; lean_object* v_quotContext_1908_; lean_object* v_currMacroScope_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_ref_1907_ = lean_ctor_get(v___y_1886_, 5);
v_quotContext_1908_ = lean_ctor_get(v___y_1886_, 10);
v_currMacroScope_1909_ = lean_ctor_get(v___y_1886_, 11);
v___x_1910_ = 0;
v___x_1911_ = l_Lean_SourceInfo_fromRef(v_ref_1907_, v___x_1910_);
v___x_1912_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1);
v___x_1913_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3));
lean_inc(v_currMacroScope_1909_);
lean_inc(v_quotContext_1908_);
v___x_1914_ = l_Lean_addMacroScope(v_quotContext_1908_, v___x_1913_, v_currMacroScope_1909_);
v___x_1915_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7));
v___x_1916_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1911_);
lean_ctor_set(v___x_1916_, 1, v___x_1912_);
lean_ctor_set(v___x_1916_, 2, v___x_1914_);
lean_ctor_set(v___x_1916_, 3, v___x_1915_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
v___x_1917_ = lean_apply_8(v_snd_1903_, v___x_1916_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, lean_box(0));
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v_ctorArgs1_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1966_ = lean_array_get_size(v_fst_1898_);
v___x_1967_ = lean_nat_dec_eq(v___x_1966_, v___x_1891_);
if (v___x_1967_ == 0)
{
v_ctorArgs1_1920_ = v_fst_1898_;
v___y_1921_ = v___y_1882_;
v___y_1922_ = v___y_1883_;
v___y_1923_ = v___y_1884_;
v___y_1924_ = v___y_1885_;
v___y_1925_ = v___y_1886_;
v___y_1926_ = v___y_1887_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1968_; 
lean_inc_ref(v___f_1879_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
v___x_1968_ = lean_apply_7(v___f_1879_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, lean_box(0));
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc_n(v_a_1969_, 7);
lean_dec_ref_known(v___x_1968_, 1);
v___x_1970_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5));
v___x_1971_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_1972_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_1973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1973_, 0, v_a_1969_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_1975_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_1976_ = lean_box(0);
lean_inc(v_currMacroScope_1909_);
lean_inc(v_quotContext_1908_);
v___x_1977_ = l_Lean_addMacroScope(v_quotContext_1908_, v___x_1976_, v_currMacroScope_1909_);
v___x_1978_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33));
v___x_1979_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1979_, 0, v_a_1969_);
lean_ctor_set(v___x_1979_, 1, v___x_1975_);
lean_ctor_set(v___x_1979_, 2, v___x_1977_);
lean_ctor_set(v___x_1979_, 3, v___x_1978_);
v___x_1980_ = l_Lean_Syntax_node1(v_a_1969_, v___x_1974_, v___x_1979_);
v___x_1981_ = l_Lean_Syntax_node2(v_a_1969_, v___x_1971_, v___x_1973_, v___x_1980_);
v___x_1982_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1983_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_1984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1984_, 0, v_a_1969_);
lean_ctor_set(v___x_1984_, 1, v___x_1982_);
lean_ctor_set(v___x_1984_, 2, v___x_1983_);
v___x_1985_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_1986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1986_, 0, v_a_1969_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = l_Lean_Syntax_node3(v_a_1969_, v___x_1970_, v___x_1981_, v___x_1984_, v___x_1986_);
v___x_1988_ = lean_array_push(v_fst_1898_, v___x_1987_);
v_ctorArgs1_1920_ = v___x_1988_;
v___y_1921_ = v___y_1882_;
v___y_1922_ = v___y_1883_;
v___y_1923_ = v___y_1884_;
v___y_1924_ = v___y_1885_;
v___y_1925_ = v___y_1886_;
v___y_1926_ = v___y_1887_;
goto v___jp_1919_;
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_a_1918_);
lean_del_object(v___x_1905_);
lean_dec(v_fst_1902_);
lean_del_object(v___x_1900_);
lean_dec(v_fst_1898_);
lean_dec_ref(v___f_1879_);
v_a_1989_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1968_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1968_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
v___jp_1919_:
{
lean_object* v___x_1927_; 
lean_inc(v___y_1926_);
lean_inc_ref(v___y_1925_);
lean_inc(v___y_1924_);
lean_inc_ref(v___y_1923_);
lean_inc(v___y_1922_);
lean_inc_ref(v___y_1921_);
v___x_1927_ = lean_apply_7(v___f_1879_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, lean_box(0));
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1957_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1957_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1957_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1932_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10));
v___x_1933_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8));
lean_inc(v_a_1928_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 2);
lean_ctor_set(v___x_1905_, 1, v___x_1933_);
lean_ctor_set(v___x_1905_, 0, v_a_1928_);
v___x_1935_ = v___x_1905_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1928_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1936_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0));
v___x_1937_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1));
lean_inc(v_a_1928_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set_tag(v___x_1900_, 2);
lean_ctor_set(v___x_1900_, 1, v___x_1936_);
lean_ctor_set(v___x_1900_, 0, v_a_1928_);
v___x_1939_ = v___x_1900_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1928_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v___x_1936_);
v___x_1939_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1940_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3));
v___x_1941_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1942_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_1943_ = l_Array_append___redArg(v___x_1942_, v_ctorArgs1_1920_);
lean_dec_ref(v_ctorArgs1_1920_);
v___x_1944_ = l_Array_append___redArg(v___x_1943_, v_fst_1902_);
lean_dec(v_fst_1902_);
lean_inc_n(v_a_1928_, 5);
v___x_1945_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1945_, 0, v_a_1928_);
lean_ctor_set(v___x_1945_, 1, v___x_1941_);
lean_ctor_set(v___x_1945_, 2, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1946_, 0, v_a_1928_);
lean_ctor_set(v___x_1946_, 1, v___x_1941_);
lean_ctor_set(v___x_1946_, 2, v___x_1942_);
v___x_1947_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_1948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1948_, 0, v_a_1928_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = l_Lean_Syntax_node4(v_a_1928_, v___x_1940_, v___x_1945_, v___x_1946_, v___x_1948_, v_a_1918_);
v___x_1950_ = l_Lean_Syntax_node2(v_a_1928_, v___x_1937_, v___x_1939_, v___x_1949_);
v___x_1951_ = l_Lean_Syntax_node2(v_a_1928_, v___x_1932_, v___x_1935_, v___x_1950_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1951_);
v___x_1953_ = v___x_1930_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v_ctorArgs1_1920_);
lean_dec(v_a_1918_);
lean_del_object(v___x_1905_);
lean_dec(v_fst_1902_);
lean_del_object(v___x_1900_);
v_a_1958_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1927_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1927_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
else
{
lean_del_object(v___x_1905_);
lean_dec(v_fst_1902_);
lean_del_object(v___x_1900_);
lean_dec(v_fst_1898_);
lean_dec_ref(v___f_1879_);
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v___f_1879_);
v_a_1999_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1895_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1895_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec_ref(v___f_1879_);
lean_dec_ref(v___f_1876_);
v_a_2007_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1889_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1889_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___boxed(lean_object* v___f_2015_, lean_object* v_numFields_2016_, lean_object* v_indVal_2017_, lean_object* v___f_2018_, lean_object* v_xs_2019_, lean_object* v_type_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2(v___f_2015_, v_numFields_2016_, v_indVal_2017_, v___f_2018_, v_xs_2019_, v_type_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v_xs_2019_);
lean_dec_ref(v_indVal_2017_);
lean_dec(v_numFields_2016_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0(lean_object* v___x_2029_, lean_object* v_ctors_2030_, lean_object* v___f_2031_, lean_object* v_indVal_2032_, lean_object* v___f_2033_, lean_object* v_x_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = l_List_get_x21Internal___redArg(v___x_2029_, v_ctors_2030_, v_x_2034_);
v___x_2043_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v___x_2042_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v_toConstantVal_2045_; lean_object* v_numFields_2046_; lean_object* v_type_2047_; lean_object* v___f_2048_; uint8_t v___x_2049_; lean_object* v___x_2050_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v_toConstantVal_2045_ = lean_ctor_get(v_a_2044_, 0);
lean_inc_ref(v_toConstantVal_2045_);
v_numFields_2046_ = lean_ctor_get(v_a_2044_, 4);
lean_inc(v_numFields_2046_);
lean_dec(v_a_2044_);
v_type_2047_ = lean_ctor_get(v_toConstantVal_2045_, 2);
lean_inc_ref(v_type_2047_);
lean_dec_ref(v_toConstantVal_2045_);
v___f_2048_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___boxed), 13, 4);
lean_closure_set(v___f_2048_, 0, v___f_2031_);
lean_closure_set(v___f_2048_, 1, v_numFields_2046_);
lean_closure_set(v___f_2048_, 2, v_indVal_2032_);
lean_closure_set(v___f_2048_, 3, v___f_2033_);
v___x_2049_ = 0;
v___x_2050_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_2047_, v___f_2048_, v___x_2049_, v___x_2049_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
return v___x_2050_;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref(v___f_2033_);
lean_dec_ref(v_indVal_2032_);
lean_dec_ref(v___f_2031_);
v_a_2051_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2043_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2043_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0___boxed(lean_object* v___x_2059_, lean_object* v_ctors_2060_, lean_object* v___f_2061_, lean_object* v_indVal_2062_, lean_object* v___f_2063_, lean_object* v_x_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0(v___x_2059_, v_ctors_2060_, v___f_2061_, v_indVal_2062_, v___f_2063_, v_x_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v_ctors_2060_);
lean_dec(v___x_2059_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(lean_object* v_f_2073_, lean_object* v_n_2074_, lean_object* v_x_2075_, lean_object* v_i_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_nat_dec_lt(v_i_2076_, v_n_2074_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_dec(v_i_2076_);
lean_dec_ref(v_f_2073_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_x_2075_);
return v___x_2085_;
}
else
{
lean_object* v___x_2086_; 
lean_inc_ref(v_f_2073_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
lean_inc(v_i_2076_);
v___x_2086_ = lean_apply_8(v_f_2073_, v_i_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, lean_box(0));
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2088_ = lean_array_push(v_x_2075_, v_a_2087_);
v___x_2089_ = lean_unsigned_to_nat(1u);
v___x_2090_ = lean_nat_add(v_i_2076_, v___x_2089_);
lean_dec(v_i_2076_);
v_x_2075_ = v___x_2088_;
v_i_2076_ = v___x_2090_;
goto _start;
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec(v_i_2076_);
lean_dec_ref(v_x_2075_);
lean_dec_ref(v_f_2073_);
v_a_2092_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2086_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2086_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg___boxed(lean_object* v_f_2100_, lean_object* v_n_2101_, lean_object* v_x_2102_, lean_object* v_i_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2100_, v_n_2101_, v_x_2102_, v_i_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v_n_2101_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(lean_object* v_n_2112_, lean_object* v_f_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = lean_mk_empty_array_with_capacity(v_n_2112_);
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2113_, v_n_2112_, v___x_2121_, v___x_2122_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg___boxed(lean_object* v_n_2124_, lean_object* v_f_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v_n_2124_, v_f_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v_n_2124_);
return v_res_2133_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2137_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__2));
v___x_2138_ = lean_unsigned_to_nat(2u);
v___x_2139_ = lean_unsigned_to_nat(87u);
v___x_2140_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__1));
v___x_2141_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__0));
v___x_2142_ = l_mkPanicMessageWithDecl(v___x_2141_, v___x_2140_, v___x_2139_, v___x_2138_, v___x_2137_);
return v___x_2142_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8));
v___x_2154_ = l_String_toRawSubstring_x27(v___x_2153_);
return v___x_2154_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__26));
v___x_2202_ = l_String_toRawSubstring_x27(v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36));
v___x_2224_ = l_String_toRawSubstring_x27(v___x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(lean_object* v_header_2233_, lean_object* v_indVal_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_targetNames_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2436_; 
v_targetNames_2242_ = lean_ctor_get(v_header_2233_, 2);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_header_2233_);
if (v_isSharedCheck_2436_ == 0)
{
lean_object* v_unused_2437_; lean_object* v_unused_2438_; lean_object* v_unused_2439_; 
v_unused_2437_ = lean_ctor_get(v_header_2233_, 3);
lean_dec(v_unused_2437_);
v_unused_2438_ = lean_ctor_get(v_header_2233_, 1);
lean_dec(v_unused_2438_);
v_unused_2439_ = lean_ctor_get(v_header_2233_, 0);
lean_dec(v_unused_2439_);
v___x_2244_ = v_header_2233_;
v_isShared_2245_ = v_isSharedCheck_2436_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_targetNames_2242_);
lean_dec(v_header_2233_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2436_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v___x_2246_ = lean_array_get_size(v_targetNames_2242_);
v___x_2247_ = lean_unsigned_to_nat(2u);
v___x_2248_ = lean_nat_dec_eq(v___x_2246_, v___x_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_del_object(v___x_2244_);
lean_dec_ref(v_targetNames_2242_);
lean_dec_ref(v_indVal_2234_);
v___x_2249_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3);
v___x_2250_ = l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0(v___x_2249_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
return v___x_2250_;
}
else
{
lean_object* v_toConstantVal_2251_; lean_object* v_ctors_2252_; lean_object* v_name_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2433_; 
v_toConstantVal_2251_ = lean_ctor_get(v_indVal_2234_, 0);
lean_inc_ref(v_toConstantVal_2251_);
v_ctors_2252_ = lean_ctor_get(v_indVal_2234_, 4);
v_name_2253_ = lean_ctor_get(v_toConstantVal_2251_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_toConstantVal_2251_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; lean_object* v_unused_2435_; 
v_unused_2434_ = lean_ctor_get(v_toConstantVal_2251_, 2);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v_toConstantVal_2251_, 1);
lean_dec(v_unused_2435_);
v___x_2255_ = v_toConstantVal_2251_;
v_isShared_2256_ = v_isSharedCheck_2433_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_name_2253_);
lean_dec(v_toConstantVal_2251_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2433_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v_ctorIdxName_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_inc_n(v_name_2253_, 2);
v_ctorIdxName_2257_ = l_Lean_mkCtorIdxName(v_name_2253_);
v___x_2258_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__5));
v___x_2259_ = l_Lean_Name_append(v_name_2253_, v___x_2258_);
v___x_2260_ = l_Lean_Core_mkFreshUserName(v___x_2259_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc_n(v_a_2261_, 2);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2262_ = l_Lean_mkCasesOnSameCtor(v_a_2261_, v_name_2253_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___f_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_dec_ref_known(v___x_2262_, 1);
v___f_2263_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1));
v___f_2264_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0));
v___x_2265_ = lean_box(0);
lean_inc_ref(v_indVal_2234_);
lean_inc(v_ctors_2252_);
v___f_2266_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0___boxed), 13, 5);
lean_closure_set(v___f_2266_, 0, v___x_2265_);
lean_closure_set(v___f_2266_, 1, v_ctors_2252_);
lean_closure_set(v___f_2266_, 2, v___f_2264_);
lean_closure_set(v___f_2266_, 3, v_indVal_2234_);
lean_closure_set(v___f_2266_, 4, v___f_2263_);
v___x_2267_ = l_Lean_InductiveVal_numCtors(v_indVal_2234_);
lean_dec_ref(v_indVal_2234_);
v___x_2268_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v___x_2267_, v___f_2266_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2408_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2408_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2408_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v_x1_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v_x2_2278_; uint8_t v___x_2279_; 
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = lean_array_get_borrowed(v___x_2265_, v_targetNames_2242_, v___x_2273_);
lean_inc(v___x_2274_);
v_x1_2275_ = l_Lean_mkIdent(v___x_2274_);
v___x_2276_ = lean_unsigned_to_nat(1u);
v___x_2277_ = lean_array_get(v___x_2265_, v_targetNames_2242_, v___x_2276_);
lean_dec_ref(v_targetNames_2242_);
v_x2_2278_ = l_Lean_mkIdent(v___x_2277_);
v___x_2279_ = lean_nat_dec_eq(v___x_2267_, v___x_2276_);
lean_dec(v___x_2267_);
if (v___x_2279_ == 0)
{
lean_object* v_ref_2280_; lean_object* v_quotContext_2281_; lean_object* v_currMacroScope_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v_ref_2280_ = lean_ctor_get(v_a_2239_, 5);
v_quotContext_2281_ = lean_ctor_get(v_a_2239_, 10);
v_currMacroScope_2282_ = lean_ctor_get(v_a_2239_, 11);
v___x_2283_ = l_Lean_SourceInfo_fromRef(v_ref_2280_, v___x_2279_);
v___x_2284_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0));
v___x_2285_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1));
lean_inc_n(v___x_2283_, 2);
v___x_2286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2283_);
lean_ctor_set(v___x_2286_, 1, v___x_2284_);
v___x_2287_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2288_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
if (v_isShared_2256_ == 0)
{
lean_ctor_set_tag(v___x_2255_, 1);
lean_ctor_set(v___x_2255_, 2, v___x_2288_);
lean_ctor_set(v___x_2255_, 1, v___x_2287_);
lean_ctor_set(v___x_2255_, 0, v___x_2283_);
v___x_2290_ = v___x_2255_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2383_, 2, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2291_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7));
v___x_2292_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9);
v___x_2293_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__10));
lean_inc(v_currMacroScope_2282_);
lean_inc(v_quotContext_2281_);
v___x_2294_ = l_Lean_addMacroScope(v_quotContext_2281_, v___x_2293_, v_currMacroScope_2282_);
v___x_2295_ = lean_box(0);
lean_inc(v___x_2283_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set_tag(v___x_2244_, 3);
lean_ctor_set(v___x_2244_, 3, v___x_2295_);
lean_ctor_set(v___x_2244_, 2, v___x_2294_);
lean_ctor_set(v___x_2244_, 1, v___x_2292_);
lean_ctor_set(v___x_2244_, 0, v___x_2283_);
v___x_2297_ = v___x_2244_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2382_, 2, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2382_, 3, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2298_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
lean_inc_n(v___x_2283_, 41);
v___x_2299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2283_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
lean_inc_ref(v___x_2297_);
v___x_2300_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2287_, v___x_2297_, v___x_2299_);
v___x_2301_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_2302_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_2303_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
lean_inc_n(v_currMacroScope_2282_, 6);
lean_inc_n(v_quotContext_2281_, 6);
v___x_2304_ = l_Lean_addMacroScope(v_quotContext_2281_, v___x_2303_, v_currMacroScope_2282_);
v___x_2305_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13));
v___x_2306_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2283_);
lean_ctor_set(v___x_2306_, 1, v___x_2302_);
lean_ctor_set(v___x_2306_, 2, v___x_2304_);
lean_ctor_set(v___x_2306_, 3, v___x_2305_);
v___x_2307_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16));
v___x_2308_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_2309_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_2310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2283_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_2312_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_2313_ = l_Lean_addMacroScope(v_quotContext_2281_, v___x_2265_, v_currMacroScope_2282_);
v___x_2314_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__16));
v___x_2315_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2283_);
lean_ctor_set(v___x_2315_, 1, v___x_2312_);
lean_ctor_set(v___x_2315_, 2, v___x_2313_);
lean_ctor_set(v___x_2315_, 3, v___x_2314_);
v___x_2316_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2311_, v___x_2315_);
v___x_2317_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2308_, v___x_2310_, v___x_2316_);
v___x_2318_ = l_Lean_mkCIdent(v_ctorIdxName_2257_);
lean_inc(v_x1_2275_);
v___x_2319_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2287_, v_x1_2275_);
lean_inc(v___x_2318_);
v___x_2320_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2301_, v___x_2318_, v___x_2319_);
v___x_2321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_2322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2283_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
lean_inc_ref_n(v___x_2322_, 2);
lean_inc_n(v___x_2317_, 2);
v___x_2323_ = l_Lean_Syntax_node3(v___x_2283_, v___x_2307_, v___x_2317_, v___x_2320_, v___x_2322_);
lean_inc(v_x2_2278_);
v___x_2324_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2287_, v_x2_2278_);
v___x_2325_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2301_, v___x_2318_, v___x_2324_);
v___x_2326_ = l_Lean_Syntax_node3(v___x_2283_, v___x_2307_, v___x_2317_, v___x_2325_, v___x_2322_);
v___x_2327_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2287_, v___x_2323_, v___x_2326_);
v___x_2328_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2301_, v___x_2306_, v___x_2327_);
v___x_2329_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2291_, v___x_2300_, v___x_2328_);
v___x_2330_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2287_, v___x_2329_);
v___x_2331_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2));
v___x_2332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2283_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4));
v___x_2334_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25));
v___x_2335_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12));
v___x_2336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2283_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20);
v___x_2338_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16));
v___x_2339_ = l_Lean_addMacroScope(v_quotContext_2281_, v___x_2338_, v_currMacroScope_2282_);
v___x_2340_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19));
v___x_2341_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2283_);
lean_ctor_set(v___x_2341_, 1, v___x_2337_);
lean_ctor_set(v___x_2341_, 2, v___x_2339_);
lean_ctor_set(v___x_2341_, 3, v___x_2340_);
lean_inc_ref(v___x_2341_);
v___x_2342_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2287_, v___x_2341_);
v___x_2343_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2287_, v___x_2342_);
v___x_2344_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_2345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2283_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
lean_inc_ref_n(v___x_2345_, 2);
lean_inc_ref_n(v___x_2336_, 2);
v___x_2346_ = l_Lean_Syntax_node4(v___x_2283_, v___x_2334_, v___x_2336_, v___x_2343_, v___x_2345_, v___x_2341_);
v___x_2347_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27);
v___x_2348_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29));
v___x_2349_ = l_Lean_addMacroScope(v_quotContext_2281_, v___x_2348_, v_currMacroScope_2282_);
v___x_2350_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22));
v___x_2351_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2283_);
lean_ctor_set(v___x_2351_, 1, v___x_2347_);
lean_ctor_set(v___x_2351_, 2, v___x_2349_);
lean_ctor_set(v___x_2351_, 3, v___x_2350_);
lean_inc_ref(v___x_2351_);
v___x_2352_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2287_, v___x_2351_);
v___x_2353_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2287_, v___x_2352_);
v___x_2354_ = l_Lean_Syntax_node4(v___x_2283_, v___x_2334_, v___x_2336_, v___x_2353_, v___x_2345_, v___x_2351_);
v___x_2355_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1);
v___x_2356_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3));
v___x_2357_ = l_Lean_addMacroScope(v_quotContext_2281_, v___x_2356_, v_currMacroScope_2282_);
v___x_2358_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__25));
v___x_2359_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2283_);
lean_ctor_set(v___x_2359_, 1, v___x_2355_);
lean_ctor_set(v___x_2359_, 2, v___x_2357_);
lean_ctor_set(v___x_2359_, 3, v___x_2358_);
v___x_2360_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2287_, v___x_2359_);
v___x_2361_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2287_, v___x_2360_);
v___x_2362_ = l_Lean_mkCIdent(v_a_2261_);
v___x_2363_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27);
v___x_2364_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31));
v___x_2365_ = l_Lean_addMacroScope(v_quotContext_2281_, v___x_2364_, v_currMacroScope_2282_);
v___x_2366_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__35));
v___x_2367_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2283_);
lean_ctor_set(v___x_2367_, 1, v___x_2363_);
lean_ctor_set(v___x_2367_, 2, v___x_2365_);
lean_ctor_set(v___x_2367_, 3, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2287_, v___x_2297_);
v___x_2369_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2301_, v___x_2367_, v___x_2368_);
v___x_2370_ = l_Lean_Syntax_node3(v___x_2283_, v___x_2307_, v___x_2317_, v___x_2369_, v___x_2322_);
v___x_2371_ = l_Array_mkArray3___redArg(v_x1_2275_, v_x2_2278_, v___x_2370_);
v___x_2372_ = l_Array_append___redArg(v___x_2371_, v_a_2269_);
lean_dec(v_a_2269_);
v___x_2373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2283_);
lean_ctor_set(v___x_2373_, 1, v___x_2287_);
lean_ctor_set(v___x_2373_, 2, v___x_2372_);
v___x_2374_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2301_, v___x_2362_, v___x_2373_);
v___x_2375_ = l_Lean_Syntax_node4(v___x_2283_, v___x_2334_, v___x_2336_, v___x_2361_, v___x_2345_, v___x_2374_);
v___x_2376_ = l_Lean_Syntax_node3(v___x_2283_, v___x_2287_, v___x_2346_, v___x_2354_, v___x_2375_);
v___x_2377_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2333_, v___x_2376_);
lean_inc_ref(v___x_2290_);
v___x_2378_ = l_Lean_Syntax_node6(v___x_2283_, v___x_2285_, v___x_2286_, v___x_2290_, v___x_2290_, v___x_2330_, v___x_2332_, v___x_2377_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2378_);
v___x_2380_ = v___x_2271_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
else
{
lean_object* v_ref_2384_; lean_object* v_quotContext_2385_; lean_object* v_currMacroScope_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_dec(v_ctorIdxName_2257_);
v_ref_2384_ = lean_ctor_get(v_a_2239_, 5);
v_quotContext_2385_ = lean_ctor_get(v_a_2239_, 10);
v_currMacroScope_2386_ = lean_ctor_get(v_a_2239_, 11);
v___x_2387_ = 0;
v___x_2388_ = l_Lean_SourceInfo_fromRef(v_ref_2384_, v___x_2387_);
v___x_2389_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_2390_ = l_Lean_mkCIdent(v_a_2261_);
v___x_2391_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2392_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37);
v___x_2393_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38));
lean_inc(v_currMacroScope_2386_);
lean_inc(v_quotContext_2385_);
v___x_2394_ = l_Lean_addMacroScope(v_quotContext_2385_, v___x_2393_, v_currMacroScope_2386_);
v___x_2395_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__40));
lean_inc(v___x_2388_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set_tag(v___x_2244_, 3);
lean_ctor_set(v___x_2244_, 3, v___x_2395_);
lean_ctor_set(v___x_2244_, 2, v___x_2394_);
lean_ctor_set(v___x_2244_, 1, v___x_2392_);
lean_ctor_set(v___x_2244_, 0, v___x_2388_);
v___x_2397_ = v___x_2244_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2401_; 
v___x_2398_ = l_Array_mkArray3___redArg(v_x1_2275_, v_x2_2278_, v___x_2397_);
v___x_2399_ = l_Array_append___redArg(v___x_2398_, v_a_2269_);
lean_dec(v_a_2269_);
lean_inc(v___x_2388_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set_tag(v___x_2255_, 1);
lean_ctor_set(v___x_2255_, 2, v___x_2399_);
lean_ctor_set(v___x_2255_, 1, v___x_2391_);
lean_ctor_set(v___x_2255_, 0, v___x_2388_);
v___x_2401_ = v___x_2255_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2406_, 2, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2402_ = l_Lean_Syntax_node2(v___x_2388_, v___x_2389_, v___x_2390_, v___x_2401_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2402_);
v___x_2404_ = v___x_2271_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v___x_2267_);
lean_dec(v_a_2261_);
lean_dec(v_ctorIdxName_2257_);
lean_del_object(v___x_2255_);
lean_del_object(v___x_2244_);
lean_dec_ref(v_targetNames_2242_);
v_a_2409_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2268_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2268_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
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
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v_a_2261_);
lean_dec(v_ctorIdxName_2257_);
lean_del_object(v___x_2255_);
lean_del_object(v___x_2244_);
lean_dec_ref(v_targetNames_2242_);
lean_dec_ref(v_indVal_2234_);
v_a_2417_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2262_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2262_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_ctorIdxName_2257_);
lean_del_object(v___x_2255_);
lean_dec(v_name_2253_);
lean_del_object(v___x_2244_);
lean_dec_ref(v_targetNames_2242_);
lean_dec_ref(v_indVal_2234_);
v_a_2425_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2260_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2260_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___boxed(lean_object* v_header_2440_, lean_object* v_indVal_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(v_header_2440_, v_indVal_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(lean_object* v_upperBound_2450_, lean_object* v_indVal_2451_, lean_object* v_xs_2452_, lean_object* v_a_2453_, lean_object* v_inst_2454_, lean_object* v_R_2455_, lean_object* v_a_2456_, lean_object* v_b_2457_, lean_object* v_c_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___redArg(v_upperBound_2450_, v_indVal_2451_, v_xs_2452_, v_a_2453_, v_a_2456_, v_b_2457_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___boxed(lean_object* v_upperBound_2467_, lean_object* v_indVal_2468_, lean_object* v_xs_2469_, lean_object* v_a_2470_, lean_object* v_inst_2471_, lean_object* v_R_2472_, lean_object* v_a_2473_, lean_object* v_b_2474_, lean_object* v_c_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(v_upperBound_2467_, v_indVal_2468_, v_xs_2469_, v_a_2470_, v_inst_2471_, v_R_2472_, v_a_2473_, v_b_2474_, v_c_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v_a_2470_);
lean_dec_ref(v_xs_2469_);
lean_dec_ref(v_indVal_2468_);
lean_dec(v_upperBound_2467_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2(lean_object* v_00_u03b1_2484_, lean_object* v_n_2485_, lean_object* v_f_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v_n_2485_, v_f_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___boxed(lean_object* v_00_u03b1_2495_, lean_object* v_n_2496_, lean_object* v_f_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2(v_00_u03b1_2495_, v_n_2496_, v_f_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v_n_2496_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2(lean_object* v_00_u03b1_2506_, lean_object* v_f_2507_, lean_object* v_n_2508_, lean_object* v_x_2509_, lean_object* v_i_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2507_, v_n_2508_, v_x_2509_, v_i_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2519_, lean_object* v_f_2520_, lean_object* v_n_2521_, lean_object* v_x_2522_, lean_object* v_i_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2(v_00_u03b1_2519_, v_f_2520_, v_n_2521_, v_x_2522_, v_i_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v_n_2521_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(lean_object* v_opts_2532_, lean_object* v_opt_2533_){
_start:
{
lean_object* v_name_2534_; lean_object* v_defValue_2535_; lean_object* v_map_2536_; lean_object* v___x_2537_; 
v_name_2534_ = lean_ctor_get(v_opt_2533_, 0);
v_defValue_2535_ = lean_ctor_get(v_opt_2533_, 1);
v_map_2536_ = lean_ctor_get(v_opts_2532_, 0);
v___x_2537_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2536_, v_name_2534_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_inc(v_defValue_2535_);
return v_defValue_2535_;
}
else
{
lean_object* v_val_2538_; 
v_val_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_val_2538_);
lean_dec_ref_known(v___x_2537_, 1);
if (lean_obj_tag(v_val_2538_) == 3)
{
lean_object* v_v_2539_; 
v_v_2539_ = lean_ctor_get(v_val_2538_, 0);
lean_inc(v_v_2539_);
lean_dec_ref_known(v_val_2538_, 1);
return v_v_2539_;
}
else
{
lean_dec(v_val_2538_);
lean_inc(v_defValue_2535_);
return v_defValue_2535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0___boxed(lean_object* v_opts_2540_, lean_object* v_opt_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(v_opts_2540_, v_opt_2541_);
lean_dec_ref(v_opt_2541_);
lean_dec_ref(v_opts_2540_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(lean_object* v_header_2543_, lean_object* v_indVal_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_options_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v_options_2552_ = lean_ctor_get(v_a_2549_, 2);
v___x_2553_ = l___private_Lean_Elab_Deriving_Ord_0__deriving_ord_linear__construction__threshold;
v___x_2554_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(v_options_2552_, v___x_2553_);
v___x_2555_ = l_Lean_InductiveVal_numCtors(v_indVal_2544_);
v___x_2556_ = lean_nat_dec_le(v___x_2554_, v___x_2555_);
lean_dec(v___x_2555_);
lean_dec(v___x_2554_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; 
v___x_2557_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(v_header_2543_, v_indVal_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2557_;
}
else
{
lean_object* v___x_2558_; 
v___x_2558_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(v_header_2543_, v_indVal_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch___boxed(lean_object* v_header_2559_, lean_object* v_indVal_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(v_header_2559_, v_indVal_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
return v_res_2568_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6));
v___x_2608_ = l_String_toRawSubstring_x27(v___x_2607_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(lean_object* v_ctx_2642_, lean_object* v_i_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_typeInfos_2651_; lean_object* v_auxFunNames_2652_; uint8_t v_usePartial_2653_; lean_object* v___x_2654_; lean_object* v_indVal_2655_; lean_object* v___x_2656_; 
v_typeInfos_2651_ = lean_ctor_get(v_ctx_2642_, 1);
v_auxFunNames_2652_ = lean_ctor_get(v_ctx_2642_, 2);
v_usePartial_2653_ = lean_ctor_get_uint8(v_ctx_2642_, sizeof(void*)*3);
v___x_2654_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_2655_ = lean_array_get_borrowed(v___x_2654_, v_typeInfos_2651_, v_i_2643_);
lean_inc(v_indVal_2655_);
v___x_2656_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader(v_indVal_2655_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc_n(v_a_2657_, 2);
lean_dec_ref_known(v___x_2656_, 1);
lean_inc(v_indVal_2655_);
v___x_2658_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(v_a_2657_, v_indVal_2655_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2790_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2790_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2790_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v_auxFunName_2664_; lean_object* v_body_2666_; lean_object* v___y_2667_; 
v___x_2663_ = lean_box(0);
v_auxFunName_2664_ = lean_array_get_borrowed(v___x_2663_, v_auxFunNames_2652_, v_i_2643_);
if (v_usePartial_2653_ == 0)
{
v_body_2666_ = v_a_2659_;
v___y_2667_ = v_a_2648_;
goto v___jp_2665_;
}
else
{
lean_object* v_argNames_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_argNames_2776_ = lean_ctor_get(v_a_2657_, 1);
v___x_2777_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
lean_inc_ref(v_argNames_2776_);
v___x_2778_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2642_, v___x_2777_, v_argNames_2776_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = l_Lean_Elab_Deriving_mkLet(v_a_2779_, v_a_2659_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
lean_dec(v_a_2779_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v_body_2666_ = v_a_2781_;
v___y_2667_ = v_a_2648_;
goto v___jp_2665_;
}
else
{
lean_del_object(v___x_2661_);
lean_dec(v_a_2657_);
return v___x_2780_;
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_del_object(v___x_2661_);
lean_dec(v_a_2659_);
lean_dec(v_a_2657_);
v_a_2782_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2778_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2778_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
v___jp_2665_:
{
if (v_usePartial_2653_ == 0)
{
lean_object* v_binders_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2715_; 
v_binders_2668_ = lean_ctor_get(v_a_2657_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_a_2657_);
if (v_isSharedCheck_2715_ == 0)
{
lean_object* v_unused_2716_; lean_object* v_unused_2717_; lean_object* v_unused_2718_; 
v_unused_2716_ = lean_ctor_get(v_a_2657_, 3);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_a_2657_, 2);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_a_2657_, 1);
lean_dec(v_unused_2718_);
v___x_2670_ = v_a_2657_;
v_isShared_2671_ = v_isSharedCheck_2715_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_binders_2668_);
lean_dec(v_a_2657_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2715_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_ref_2672_; lean_object* v_quotContext_2673_; lean_object* v_currMacroScope_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v_ref_2672_ = lean_ctor_get(v___y_2667_, 5);
v_quotContext_2673_ = lean_ctor_get(v___y_2667_, 10);
v_currMacroScope_2674_ = lean_ctor_get(v___y_2667_, 11);
v___x_2675_ = l_Lean_SourceInfo_fromRef(v_ref_2672_, v_usePartial_2653_);
v___x_2676_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_2677_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_2678_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2679_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
lean_inc_n(v___x_2675_, 7);
v___x_2680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2675_);
lean_ctor_set(v___x_2680_, 1, v___x_2678_);
lean_ctor_set(v___x_2680_, 2, v___x_2679_);
lean_inc_ref_n(v___x_2680_, 8);
v___x_2681_ = l_Lean_Syntax_node7(v___x_2675_, v___x_2677_, v___x_2680_, v___x_2680_, v___x_2680_, v___x_2680_, v___x_2680_, v___x_2680_, v___x_2680_);
v___x_2682_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_2683_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_2684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2675_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_2664_);
v___x_2686_ = l_Lean_mkIdent(v_auxFunName_2664_);
v___x_2687_ = l_Lean_Syntax_node2(v___x_2675_, v___x_2685_, v___x_2686_, v___x_2680_);
v___x_2688_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_2689_ = l_Array_append___redArg(v___x_2679_, v_binders_2668_);
lean_dec_ref(v_binders_2668_);
v___x_2690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2675_);
lean_ctor_set(v___x_2690_, 1, v___x_2678_);
lean_ctor_set(v___x_2690_, 2, v___x_2689_);
v___x_2691_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_2692_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_2693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2675_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_2695_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_2674_);
lean_inc(v_quotContext_2673_);
v___x_2696_ = l_Lean_addMacroScope(v_quotContext_2673_, v___x_2695_, v_currMacroScope_2674_);
v___x_2697_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19));
if (v_isShared_2671_ == 0)
{
lean_ctor_set_tag(v___x_2670_, 3);
lean_ctor_set(v___x_2670_, 3, v___x_2697_);
lean_ctor_set(v___x_2670_, 2, v___x_2696_);
lean_ctor_set(v___x_2670_, 1, v___x_2694_);
lean_ctor_set(v___x_2670_, 0, v___x_2675_);
v___x_2699_ = v___x_2670_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2675_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2714_, 2, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2714_, 3, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
lean_inc_n(v___x_2675_, 7);
v___x_2700_ = l_Lean_Syntax_node2(v___x_2675_, v___x_2691_, v___x_2693_, v___x_2699_);
v___x_2701_ = l_Lean_Syntax_node1(v___x_2675_, v___x_2678_, v___x_2700_);
v___x_2702_ = l_Lean_Syntax_node2(v___x_2675_, v___x_2688_, v___x_2690_, v___x_2701_);
v___x_2703_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_2704_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_2705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2675_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
lean_inc_ref_n(v___x_2680_, 3);
v___x_2707_ = l_Lean_Syntax_node2(v___x_2675_, v___x_2706_, v___x_2680_, v___x_2680_);
v___x_2708_ = l_Lean_Syntax_node4(v___x_2675_, v___x_2703_, v___x_2705_, v_body_2666_, v___x_2707_, v___x_2680_);
v___x_2709_ = l_Lean_Syntax_node5(v___x_2675_, v___x_2682_, v___x_2684_, v___x_2687_, v___x_2702_, v___x_2708_, v___x_2680_);
v___x_2710_ = l_Lean_Syntax_node2(v___x_2675_, v___x_2676_, v___x_2681_, v___x_2709_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2710_);
v___x_2712_ = v___x_2661_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
else
{
lean_object* v_binders_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2772_; 
v_binders_2719_ = lean_ctor_get(v_a_2657_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_a_2657_);
if (v_isSharedCheck_2772_ == 0)
{
lean_object* v_unused_2773_; lean_object* v_unused_2774_; lean_object* v_unused_2775_; 
v_unused_2773_ = lean_ctor_get(v_a_2657_, 3);
lean_dec(v_unused_2773_);
v_unused_2774_ = lean_ctor_get(v_a_2657_, 2);
lean_dec(v_unused_2774_);
v_unused_2775_ = lean_ctor_get(v_a_2657_, 1);
lean_dec(v_unused_2775_);
v___x_2721_ = v_a_2657_;
v_isShared_2722_ = v_isSharedCheck_2772_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_binders_2719_);
lean_dec(v_a_2657_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2772_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v_ref_2723_; lean_object* v_quotContext_2724_; lean_object* v_currMacroScope_2725_; uint8_t v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v_ref_2723_ = lean_ctor_get(v___y_2667_, 5);
v_quotContext_2724_ = lean_ctor_get(v___y_2667_, 10);
v_currMacroScope_2725_ = lean_ctor_get(v___y_2667_, 11);
v___x_2726_ = 0;
v___x_2727_ = l_Lean_SourceInfo_fromRef(v_ref_2723_, v___x_2726_);
v___x_2728_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_2729_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_2730_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2731_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
lean_inc_n(v___x_2727_, 10);
v___x_2732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2727_);
lean_ctor_set(v___x_2732_, 1, v___x_2730_);
lean_ctor_set(v___x_2732_, 2, v___x_2731_);
v___x_2733_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26));
v___x_2734_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27));
v___x_2735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2727_);
lean_ctor_set(v___x_2735_, 1, v___x_2733_);
v___x_2736_ = l_Lean_Syntax_node1(v___x_2727_, v___x_2734_, v___x_2735_);
v___x_2737_ = l_Lean_Syntax_node1(v___x_2727_, v___x_2730_, v___x_2736_);
lean_inc_ref_n(v___x_2732_, 7);
v___x_2738_ = l_Lean_Syntax_node7(v___x_2727_, v___x_2729_, v___x_2732_, v___x_2732_, v___x_2732_, v___x_2732_, v___x_2732_, v___x_2732_, v___x_2737_);
v___x_2739_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_2740_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_2741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2727_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_2664_);
v___x_2743_ = l_Lean_mkIdent(v_auxFunName_2664_);
v___x_2744_ = l_Lean_Syntax_node2(v___x_2727_, v___x_2742_, v___x_2743_, v___x_2732_);
v___x_2745_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_2746_ = l_Array_append___redArg(v___x_2731_, v_binders_2719_);
lean_dec_ref(v_binders_2719_);
v___x_2747_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2727_);
lean_ctor_set(v___x_2747_, 1, v___x_2730_);
lean_ctor_set(v___x_2747_, 2, v___x_2746_);
v___x_2748_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_2749_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_2750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2727_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_2752_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_2725_);
lean_inc(v_quotContext_2724_);
v___x_2753_ = l_Lean_addMacroScope(v_quotContext_2724_, v___x_2752_, v_currMacroScope_2725_);
v___x_2754_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19));
if (v_isShared_2722_ == 0)
{
lean_ctor_set_tag(v___x_2721_, 3);
lean_ctor_set(v___x_2721_, 3, v___x_2754_);
lean_ctor_set(v___x_2721_, 2, v___x_2753_);
lean_ctor_set(v___x_2721_, 1, v___x_2751_);
lean_ctor_set(v___x_2721_, 0, v___x_2727_);
v___x_2756_ = v___x_2721_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2727_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2771_, 2, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2771_, 3, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
lean_inc_n(v___x_2727_, 7);
v___x_2757_ = l_Lean_Syntax_node2(v___x_2727_, v___x_2748_, v___x_2750_, v___x_2756_);
v___x_2758_ = l_Lean_Syntax_node1(v___x_2727_, v___x_2730_, v___x_2757_);
v___x_2759_ = l_Lean_Syntax_node2(v___x_2727_, v___x_2745_, v___x_2747_, v___x_2758_);
v___x_2760_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_2761_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_2762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2727_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
lean_inc_ref_n(v___x_2732_, 3);
v___x_2764_ = l_Lean_Syntax_node2(v___x_2727_, v___x_2763_, v___x_2732_, v___x_2732_);
v___x_2765_ = l_Lean_Syntax_node4(v___x_2727_, v___x_2760_, v___x_2762_, v_body_2666_, v___x_2764_, v___x_2732_);
v___x_2766_ = l_Lean_Syntax_node5(v___x_2727_, v___x_2739_, v___x_2741_, v___x_2744_, v___x_2759_, v___x_2765_, v___x_2732_);
v___x_2767_ = l_Lean_Syntax_node2(v___x_2727_, v___x_2728_, v___x_2738_, v___x_2766_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2767_);
v___x_2769_ = v___x_2661_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2657_);
return v___x_2658_;
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
v_a_2791_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2656_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2656_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___boxed(lean_object* v_ctx_2799_, lean_object* v_i_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(v_ctx_2799_, v_i_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_i_2800_);
lean_dec_ref(v_ctx_2799_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_2809_, lean_object* v_ctx_2810_, lean_object* v_a_2811_, lean_object* v_b_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
uint8_t v___x_2820_; 
v___x_2820_ = lean_nat_dec_lt(v_a_2811_, v_upperBound_2809_);
if (v___x_2820_ == 0)
{
lean_object* v___x_2821_; 
lean_dec(v_a_2811_);
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_b_2812_);
return v___x_2821_;
}
else
{
lean_object* v___x_2822_; 
v___x_2822_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(v_ctx_2810_, v_a_2811_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2824_ = lean_array_push(v_b_2812_, v_a_2823_);
v___x_2825_ = lean_unsigned_to_nat(1u);
v___x_2826_ = lean_nat_add(v_a_2811_, v___x_2825_);
lean_dec(v_a_2811_);
v_a_2811_ = v___x_2826_;
v_b_2812_ = v___x_2824_;
goto _start;
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec_ref(v_b_2812_);
lean_dec(v_a_2811_);
v_a_2828_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2822_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2822_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_2836_, lean_object* v_ctx_2837_, lean_object* v_a_2838_, lean_object* v_b_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v_upperBound_2836_, v_ctx_2837_, v_a_2838_, v_b_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v_ctx_2837_);
lean_dec(v_upperBound_2836_);
return v_res_2847_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4));
v___x_2862_ = l_String_toRawSubstring_x27(v___x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(lean_object* v_ctx_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_typeInfos_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v_auxDefs_2889_; lean_object* v___x_2890_; 
v_typeInfos_2886_ = lean_ctor_get(v_ctx_2878_, 1);
v___x_2887_ = lean_array_get_size(v_typeInfos_2886_);
v___x_2888_ = lean_unsigned_to_nat(0u);
v_auxDefs_2889_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_2890_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v___x_2887_, v_ctx_2878_, v___x_2888_, v_auxDefs_2889_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2926_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2926_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2926_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v_ref_2895_; lean_object* v_quotContext_2896_; lean_object* v_currMacroScope_2897_; uint8_t v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
v_ref_2895_ = lean_ctor_get(v_a_2883_, 5);
v_quotContext_2896_ = lean_ctor_get(v_a_2883_, 10);
v_currMacroScope_2897_ = lean_ctor_get(v_a_2883_, 11);
v___x_2898_ = 0;
v___x_2899_ = l_Lean_SourceInfo_fromRef(v_ref_2895_, v___x_2898_);
v___x_2900_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0));
v___x_2901_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1));
lean_inc_n(v___x_2899_, 8);
v___x_2902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2899_);
lean_ctor_set(v___x_2902_, 1, v___x_2900_);
v___x_2903_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2904_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2));
v___x_2905_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3));
v___x_2906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2899_);
lean_ctor_set(v___x_2906_, 1, v___x_2904_);
v___x_2907_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5);
v___x_2908_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7));
lean_inc(v_currMacroScope_2897_);
lean_inc(v_quotContext_2896_);
v___x_2909_ = l_Lean_addMacroScope(v_quotContext_2896_, v___x_2908_, v_currMacroScope_2897_);
v___x_2910_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__10));
v___x_2911_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2899_);
lean_ctor_set(v___x_2911_, 1, v___x_2907_);
lean_ctor_set(v___x_2911_, 2, v___x_2909_);
lean_ctor_set(v___x_2911_, 3, v___x_2910_);
v___x_2912_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_2913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2899_);
lean_ctor_set(v___x_2913_, 1, v___x_2903_);
lean_ctor_set(v___x_2913_, 2, v___x_2912_);
v___x_2914_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__11));
v___x_2915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2899_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = l_Lean_Syntax_node4(v___x_2899_, v___x_2905_, v___x_2906_, v___x_2911_, v___x_2913_, v___x_2915_);
v___x_2917_ = l_Array_mkArray1___redArg(v___x_2916_);
v___x_2918_ = l_Array_append___redArg(v___x_2917_, v_a_2891_);
lean_dec(v_a_2891_);
v___x_2919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2899_);
lean_ctor_set(v___x_2919_, 1, v___x_2903_);
lean_ctor_set(v___x_2919_, 2, v___x_2918_);
v___x_2920_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__12));
v___x_2921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2899_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = l_Lean_Syntax_node3(v___x_2899_, v___x_2901_, v___x_2902_, v___x_2919_, v___x_2921_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2922_);
v___x_2924_ = v___x_2893_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
v_a_2927_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2890_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2890_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___boxed(lean_object* v_ctx_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(v_ctx_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
lean_dec_ref(v_ctx_2935_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0(lean_object* v_upperBound_2944_, lean_object* v_ctx_2945_, lean_object* v_inst_2946_, lean_object* v_R_2947_, lean_object* v_a_2948_, lean_object* v_b_2949_, lean_object* v_c_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v_upperBound_2944_, v_ctx_2945_, v_a_2948_, v_b_2949_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_2959_, lean_object* v_ctx_2960_, lean_object* v_inst_2961_, lean_object* v_R_2962_, lean_object* v_a_2963_, lean_object* v_b_2964_, lean_object* v_c_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0(v_upperBound_2959_, v_ctx_2960_, v_inst_2961_, v_R_2962_, v_a_2963_, v_b_2964_, v_c_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec_ref(v_ctx_2960_);
lean_dec(v_upperBound_2959_);
return v_res_2973_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2974_; double v___x_2975_; 
v___x_2974_ = lean_unsigned_to_nat(0u);
v___x_2975_ = lean_float_of_nat(v___x_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(lean_object* v_cls_2978_, lean_object* v_msg_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_ref_2985_; lean_object* v___x_2986_; lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3031_; 
v_ref_2985_ = lean_ctor_get(v___y_2982_, 5);
v___x_2986_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_3031_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3031_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v_traceState_2992_; lean_object* v_env_2993_; lean_object* v_nextMacroScope_2994_; lean_object* v_ngen_2995_; lean_object* v_auxDeclNGen_2996_; lean_object* v_cache_2997_; lean_object* v_messages_2998_; lean_object* v_infoState_2999_; lean_object* v_snapshotTasks_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3030_; 
v___x_2991_ = lean_st_ref_take(v___y_2983_);
v_traceState_2992_ = lean_ctor_get(v___x_2991_, 4);
v_env_2993_ = lean_ctor_get(v___x_2991_, 0);
v_nextMacroScope_2994_ = lean_ctor_get(v___x_2991_, 1);
v_ngen_2995_ = lean_ctor_get(v___x_2991_, 2);
v_auxDeclNGen_2996_ = lean_ctor_get(v___x_2991_, 3);
v_cache_2997_ = lean_ctor_get(v___x_2991_, 5);
v_messages_2998_ = lean_ctor_get(v___x_2991_, 6);
v_infoState_2999_ = lean_ctor_get(v___x_2991_, 7);
v_snapshotTasks_3000_ = lean_ctor_get(v___x_2991_, 8);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3002_ = v___x_2991_;
v_isShared_3003_ = v_isSharedCheck_3030_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_snapshotTasks_3000_);
lean_inc(v_infoState_2999_);
lean_inc(v_messages_2998_);
lean_inc(v_cache_2997_);
lean_inc(v_traceState_2992_);
lean_inc(v_auxDeclNGen_2996_);
lean_inc(v_ngen_2995_);
lean_inc(v_nextMacroScope_2994_);
lean_inc(v_env_2993_);
lean_dec(v___x_2991_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3030_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
uint64_t v_tid_3004_; lean_object* v_traces_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3029_; 
v_tid_3004_ = lean_ctor_get_uint64(v_traceState_2992_, sizeof(void*)*1);
v_traces_3005_ = lean_ctor_get(v_traceState_2992_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_traceState_2992_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3007_ = v_traceState_2992_;
v_isShared_3008_ = v_isSharedCheck_3029_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_traces_3005_);
lean_dec(v_traceState_2992_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3029_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; double v___x_3010_; uint8_t v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3009_ = lean_box(0);
v___x_3010_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0);
v___x_3011_ = 0;
v___x_3012_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22));
v___x_3013_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3013_, 0, v_cls_2978_);
lean_ctor_set(v___x_3013_, 1, v___x_3009_);
lean_ctor_set(v___x_3013_, 2, v___x_3012_);
lean_ctor_set_float(v___x_3013_, sizeof(void*)*3, v___x_3010_);
lean_ctor_set_float(v___x_3013_, sizeof(void*)*3 + 8, v___x_3010_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*3 + 16, v___x_3011_);
v___x_3014_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__1));
v___x_3015_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v_a_2987_);
lean_ctor_set(v___x_3015_, 2, v___x_3014_);
lean_inc(v_ref_2985_);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v_ref_2985_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = l_Lean_PersistentArray_push___redArg(v_traces_3005_, v___x_3016_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3017_);
v___x_3019_ = v___x_3007_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3017_);
lean_ctor_set_uint64(v_reuseFailAlloc_3028_, sizeof(void*)*1, v_tid_3004_);
v___x_3019_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3021_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 4, v___x_3019_);
v___x_3021_ = v___x_3002_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_env_2993_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_nextMacroScope_2994_);
lean_ctor_set(v_reuseFailAlloc_3027_, 2, v_ngen_2995_);
lean_ctor_set(v_reuseFailAlloc_3027_, 3, v_auxDeclNGen_2996_);
lean_ctor_set(v_reuseFailAlloc_3027_, 4, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3027_, 5, v_cache_2997_);
lean_ctor_set(v_reuseFailAlloc_3027_, 6, v_messages_2998_);
lean_ctor_set(v_reuseFailAlloc_3027_, 7, v_infoState_2999_);
lean_ctor_set(v_reuseFailAlloc_3027_, 8, v_snapshotTasks_3000_);
v___x_3021_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3022_ = lean_st_ref_set(v___y_2983_, v___x_3021_);
v___x_3023_ = lean_box(0);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_3023_);
v___x_3025_ = v___x_2989_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_3032_, lean_object* v_msg_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v_cls_3032_, v_msg_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
if (lean_obj_tag(v_a_3040_) == 0)
{
lean_object* v___x_3042_; 
v___x_3042_ = l_List_reverse___redArg(v_a_3041_);
return v___x_3042_;
}
else
{
lean_object* v_head_3043_; lean_object* v_tail_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3053_; 
v_head_3043_ = lean_ctor_get(v_a_3040_, 0);
v_tail_3044_ = lean_ctor_get(v_a_3040_, 1);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_a_3040_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3046_ = v_a_3040_;
v_isShared_3047_ = v_isSharedCheck_3053_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_tail_3044_);
lean_inc(v_head_3043_);
lean_dec(v_a_3040_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3053_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3048_ = l_Lean_MessageData_ofSyntax(v_head_3043_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 1, v_a_3041_);
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3050_ = v___x_3046_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3048_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_a_3041_);
v___x_3050_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
v_a_3040_ = v_tail_3044_;
v_a_3041_ = v___x_3050_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3062_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2));
v___x_3063_ = l_Lean_Name_append(v___x_3062_, v___x_3061_);
return v___x_3063_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4));
v___x_3066_ = l_Lean_stringToMessageData(v___x_3065_);
return v___x_3066_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17(void){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16));
v___x_3095_ = l_String_toRawSubstring_x27(v___x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(lean_object* v_declName_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v_cmds_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v_options_3114_; lean_object* v_inheritedTraceOptions_3115_; lean_object* v___y_3116_; uint8_t v___x_3146_; lean_object* v___x_3147_; 
v___x_3107_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_3108_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_3146_ = 0;
lean_inc(v_declName_3099_);
v___x_3147_ = l_Lean_Elab_Deriving_mkContext(v___x_3107_, v___x_3108_, v_declName_3099_, v___x_3146_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3149_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3147_, 1);
v___x_3149_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(v_a_3148_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; lean_object* v___x_3155_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc(v_a_3150_);
lean_dec_ref_known(v___x_3149_, 1);
v___x_3151_ = lean_unsigned_to_nat(1u);
v___x_3152_ = lean_mk_empty_array_with_capacity(v___x_3151_);
lean_inc_ref(v___x_3152_);
v___x_3153_ = lean_array_push(v___x_3152_, v_declName_3099_);
v___x_3154_ = 1;
lean_inc(v_a_3148_);
v___x_3155_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_3148_, v___x_3107_, v___x_3153_, v___x_3154_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
lean_dec_ref(v___x_3153_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v_instName_3157_; uint8_t v_usePartial_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3155_, 1);
v_instName_3157_ = lean_ctor_get(v_a_3148_, 0);
lean_inc(v_instName_3157_);
v_usePartial_3158_ = lean_ctor_get_uint8(v_a_3148_, sizeof(void*)*3);
lean_dec(v_a_3148_);
v___x_3159_ = lean_array_push(v___x_3152_, v_a_3150_);
v___x_3160_ = l_Array_append___redArg(v___x_3159_, v_a_3156_);
lean_dec(v_a_3156_);
if (v_usePartial_3158_ == 0)
{
lean_object* v_options_3161_; lean_object* v_ref_3162_; lean_object* v_quotContext_3163_; lean_object* v_currMacroScope_3164_; lean_object* v_inheritedTraceOptions_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_options_3161_ = lean_ctor_get(v_a_3104_, 2);
v_ref_3162_ = lean_ctor_get(v_a_3104_, 5);
v_quotContext_3163_ = lean_ctor_get(v_a_3104_, 10);
v_currMacroScope_3164_ = lean_ctor_get(v_a_3104_, 11);
v_inheritedTraceOptions_3165_ = lean_ctor_get(v_a_3104_, 13);
v___x_3166_ = l_Lean_SourceInfo_fromRef(v_ref_3162_, v_usePartial_3158_);
v___x_3167_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6));
v___x_3168_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7));
lean_inc_n(v___x_3166_, 10);
v___x_3169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3166_);
lean_ctor_set(v___x_3169_, 1, v___x_3167_);
v___x_3170_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8));
v___x_3171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3166_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_3173_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10));
v___x_3174_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12));
v___x_3175_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_3176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3166_);
lean_ctor_set(v___x_3176_, 1, v___x_3172_);
lean_ctor_set(v___x_3176_, 2, v___x_3175_);
lean_inc_ref(v___x_3176_);
v___x_3177_ = l_Lean_Syntax_node1(v___x_3166_, v___x_3174_, v___x_3176_);
v___x_3178_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15));
v___x_3179_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17);
v___x_3180_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__18));
lean_inc(v_currMacroScope_3164_);
lean_inc(v_quotContext_3163_);
v___x_3181_ = l_Lean_addMacroScope(v_quotContext_3163_, v___x_3180_, v_currMacroScope_3164_);
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3166_);
lean_ctor_set(v___x_3183_, 1, v___x_3179_);
lean_ctor_set(v___x_3183_, 2, v___x_3181_);
lean_ctor_set(v___x_3183_, 3, v___x_3182_);
v___x_3184_ = l_Lean_Syntax_node2(v___x_3166_, v___x_3178_, v___x_3183_, v___x_3176_);
v___x_3185_ = l_Lean_Syntax_node2(v___x_3166_, v___x_3173_, v___x_3177_, v___x_3184_);
v___x_3186_ = l_Lean_Syntax_node1(v___x_3166_, v___x_3172_, v___x_3185_);
v___x_3187_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__19));
v___x_3188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3166_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = l_Lean_mkIdent(v_instName_3157_);
v___x_3190_ = l_Lean_Syntax_node1(v___x_3166_, v___x_3172_, v___x_3189_);
v___x_3191_ = l_Lean_Syntax_node5(v___x_3166_, v___x_3168_, v___x_3169_, v___x_3171_, v___x_3186_, v___x_3188_, v___x_3190_);
v___x_3192_ = lean_array_push(v___x_3160_, v___x_3191_);
v_cmds_3110_ = v___x_3192_;
v___y_3111_ = v_a_3102_;
v___y_3112_ = v_a_3103_;
v___y_3113_ = v_a_3104_;
v_options_3114_ = v_options_3161_;
v_inheritedTraceOptions_3115_ = v_inheritedTraceOptions_3165_;
v___y_3116_ = v_a_3105_;
goto v___jp_3109_;
}
else
{
lean_object* v_options_3193_; lean_object* v_inheritedTraceOptions_3194_; 
lean_dec(v_instName_3157_);
v_options_3193_ = lean_ctor_get(v_a_3104_, 2);
v_inheritedTraceOptions_3194_ = lean_ctor_get(v_a_3104_, 13);
v_cmds_3110_ = v___x_3160_;
v___y_3111_ = v_a_3102_;
v___y_3112_ = v_a_3103_;
v___y_3113_ = v_a_3104_;
v_options_3114_ = v_options_3193_;
v_inheritedTraceOptions_3115_ = v_inheritedTraceOptions_3194_;
v___y_3116_ = v_a_3105_;
goto v___jp_3109_;
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec_ref(v___x_3152_);
lean_dec(v_a_3150_);
lean_dec(v_a_3148_);
v_a_3195_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3155_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3155_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v_a_3148_);
lean_dec(v_declName_3099_);
v_a_3203_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3149_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3149_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v_declName_3099_);
v_a_3211_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3147_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3147_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
v___jp_3109_:
{
uint8_t v_hasTrace_3117_; 
v_hasTrace_3117_ = lean_ctor_get_uint8(v_options_3114_, sizeof(void*)*1);
if (v_hasTrace_3117_ == 0)
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3118_, 0, v_cmds_3110_);
return v___x_3118_;
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3119_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3120_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3);
v___x_3121_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3115_, v_options_3114_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_cmds_3110_);
return v___x_3122_;
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3123_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5);
lean_inc_ref(v_cmds_3110_);
v___x_3124_ = lean_array_to_list(v_cmds_3110_);
v___x_3125_ = lean_box(0);
v___x_3126_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(v___x_3124_, v___x_3125_);
v___x_3127_ = l_Lean_MessageData_ofList(v___x_3126_);
v___x_3128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3123_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
v___x_3129_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v___x_3119_, v___x_3128_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3116_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v___x_3129_, 0);
lean_dec(v_unused_3137_);
v___x_3131_ = v___x_3129_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_dec(v___x_3129_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v_cmds_3110_);
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_cmds_3110_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec_ref(v_cmds_3110_);
v_a_3138_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3129_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3129_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___boxed(lean_object* v_declName_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(v_declName_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1(lean_object* v_cls_3228_, lean_object* v_msg_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v_cls_3228_, v_msg_3229_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___boxed(lean_object* v_cls_3238_, lean_object* v_msg_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1(v_cls_3238_, v_msg_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
return v_res_3247_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2));
v___x_3256_ = l_String_toRawSubstring_x27(v___x_3255_);
return v___x_3256_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3260_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5));
v___x_3261_ = l_String_toRawSubstring_x27(v___x_3260_);
return v___x_3261_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__11));
v___x_3275_ = l_String_toRawSubstring_x27(v___x_3274_);
return v___x_3275_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__15));
v___x_3282_ = l_String_toRawSubstring_x27(v___x_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(lean_object* v_ctx_3286_, lean_object* v_name_3287_, lean_object* v_a_3288_){
_start:
{
lean_object* v_auxFunNames_3290_; lean_object* v_ref_3291_; lean_object* v_quotContext_3292_; lean_object* v_currMacroScope_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v_auxFunName_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_auxFunNames_3290_ = lean_ctor_get(v_ctx_3286_, 2);
v_ref_3291_ = lean_ctor_get(v_a_3288_, 5);
v_quotContext_3292_ = lean_ctor_get(v_a_3288_, 10);
v_currMacroScope_3293_ = lean_ctor_get(v_a_3288_, 11);
v___x_3294_ = lean_box(0);
v___x_3295_ = lean_unsigned_to_nat(0u);
v_auxFunName_3296_ = lean_array_get_borrowed(v___x_3294_, v_auxFunNames_3290_, v___x_3295_);
v___x_3297_ = 0;
v___x_3298_ = l_Lean_SourceInfo_fromRef(v_ref_3291_, v___x_3297_);
v___x_3299_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_3300_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_3301_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_3302_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
lean_inc_n(v___x_3298_, 26);
v___x_3303_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3298_);
lean_ctor_set(v___x_3303_, 1, v___x_3301_);
lean_ctor_set(v___x_3303_, 2, v___x_3302_);
lean_inc_ref_n(v___x_3303_, 12);
v___x_3304_ = l_Lean_Syntax_node7(v___x_3298_, v___x_3300_, v___x_3303_, v___x_3303_, v___x_3303_, v___x_3303_, v___x_3303_, v___x_3303_, v___x_3303_);
v___x_3305_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_3307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3298_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3296_);
v___x_3309_ = l_Lean_mkIdent(v_auxFunName_3296_);
v___x_3310_ = l_Lean_Syntax_node2(v___x_3298_, v___x_3308_, v___x_3309_, v___x_3303_);
v___x_3311_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_3312_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1));
v___x_3313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_3314_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3298_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3);
v___x_3316_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__4));
lean_inc_n(v_currMacroScope_3293_, 6);
lean_inc_n(v_quotContext_3292_, 6);
v___x_3317_ = l_Lean_addMacroScope(v_quotContext_3292_, v___x_3316_, v_currMacroScope_3293_);
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3298_);
lean_ctor_set(v___x_3319_, 1, v___x_3315_);
lean_ctor_set(v___x_3319_, 2, v___x_3317_);
lean_ctor_set(v___x_3319_, 3, v___x_3318_);
v___x_3320_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6);
v___x_3321_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__7));
v___x_3322_ = l_Lean_addMacroScope(v_quotContext_3292_, v___x_3321_, v_currMacroScope_3293_);
v___x_3323_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3298_);
lean_ctor_set(v___x_3323_, 1, v___x_3320_);
lean_ctor_set(v___x_3323_, 2, v___x_3322_);
lean_ctor_set(v___x_3323_, 3, v___x_3318_);
v___x_3324_ = l_Lean_Syntax_node2(v___x_3298_, v___x_3301_, v___x_3319_, v___x_3323_);
v___x_3325_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_3326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3298_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = l_Lean_mkCIdent(v_name_3287_);
lean_inc_ref(v___x_3326_);
v___x_3328_ = l_Lean_Syntax_node2(v___x_3298_, v___x_3301_, v___x_3326_, v___x_3327_);
v___x_3329_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_3330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3298_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = l_Lean_Syntax_node5(v___x_3298_, v___x_3312_, v___x_3314_, v___x_3324_, v___x_3328_, v___x_3303_, v___x_3330_);
v___x_3332_ = l_Lean_Syntax_node1(v___x_3298_, v___x_3301_, v___x_3331_);
v___x_3333_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_3334_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_3335_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
v___x_3336_ = l_Lean_addMacroScope(v_quotContext_3292_, v___x_3335_, v_currMacroScope_3293_);
v___x_3337_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__10));
v___x_3338_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3298_);
lean_ctor_set(v___x_3338_, 1, v___x_3334_);
lean_ctor_set(v___x_3338_, 2, v___x_3336_);
lean_ctor_set(v___x_3338_, 3, v___x_3337_);
v___x_3339_ = l_Lean_Syntax_node2(v___x_3298_, v___x_3333_, v___x_3326_, v___x_3338_);
v___x_3340_ = l_Lean_Syntax_node1(v___x_3298_, v___x_3301_, v___x_3339_);
v___x_3341_ = l_Lean_Syntax_node2(v___x_3298_, v___x_3311_, v___x_3332_, v___x_3340_);
v___x_3342_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_3343_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_3344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3298_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_3346_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_3347_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
v___x_3348_ = l_Lean_addMacroScope(v_quotContext_3292_, v___x_3347_, v_currMacroScope_3293_);
v___x_3349_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13));
v___x_3350_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3298_);
lean_ctor_set(v___x_3350_, 1, v___x_3346_);
lean_ctor_set(v___x_3350_, 2, v___x_3348_);
lean_ctor_set(v___x_3350_, 3, v___x_3349_);
v___x_3351_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12);
v___x_3352_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14));
v___x_3353_ = l_Lean_addMacroScope(v_quotContext_3292_, v___x_3352_, v_currMacroScope_3293_);
v___x_3354_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3298_);
lean_ctor_set(v___x_3354_, 1, v___x_3351_);
lean_ctor_set(v___x_3354_, 2, v___x_3353_);
lean_ctor_set(v___x_3354_, 3, v___x_3318_);
v___x_3355_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16);
v___x_3356_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17));
v___x_3357_ = l_Lean_addMacroScope(v_quotContext_3292_, v___x_3356_, v_currMacroScope_3293_);
v___x_3358_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3298_);
lean_ctor_set(v___x_3358_, 1, v___x_3355_);
lean_ctor_set(v___x_3358_, 2, v___x_3357_);
lean_ctor_set(v___x_3358_, 3, v___x_3318_);
v___x_3359_ = l_Lean_Syntax_node2(v___x_3298_, v___x_3301_, v___x_3354_, v___x_3358_);
v___x_3360_ = l_Lean_Syntax_node2(v___x_3298_, v___x_3345_, v___x_3350_, v___x_3359_);
v___x_3361_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
v___x_3362_ = l_Lean_Syntax_node2(v___x_3298_, v___x_3361_, v___x_3303_, v___x_3303_);
v___x_3363_ = l_Lean_Syntax_node4(v___x_3298_, v___x_3342_, v___x_3344_, v___x_3360_, v___x_3362_, v___x_3303_);
v___x_3364_ = l_Lean_Syntax_node5(v___x_3298_, v___x_3305_, v___x_3307_, v___x_3310_, v___x_3341_, v___x_3363_, v___x_3303_);
v___x_3365_ = l_Lean_Syntax_node2(v___x_3298_, v___x_3299_, v___x_3304_, v___x_3364_);
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___boxed(lean_object* v_ctx_3367_, lean_object* v_name_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_ctx_3367_, v_name_3368_, v_a_3369_);
lean_dec_ref(v_a_3369_);
lean_dec_ref(v_ctx_3367_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun(lean_object* v_ctx_3372_, lean_object* v_name_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v___x_3381_; 
v___x_3381_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_ctx_3372_, v_name_3373_, v_a_3378_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___boxed(lean_object* v_ctx_3382_, lean_object* v_name_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun(v_ctx_3382_, v_name_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
lean_dec_ref(v_ctx_3382_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(lean_object* v_name_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; lean_object* v___x_3403_; 
v___x_3400_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_3401_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_3402_ = 1;
lean_inc(v_name_3392_);
v___x_3403_ = l_Lean_Elab_Deriving_mkContext(v___x_3400_, v___x_3401_, v_name_3392_, v___x_3402_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3405_; lean_object* v_a_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___x_3403_, 1);
lean_inc(v_name_3392_);
v___x_3405_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_a_3404_, v_name_3392_, v_a_3397_);
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref(v___x_3405_);
v___x_3407_ = lean_unsigned_to_nat(1u);
v___x_3408_ = lean_mk_empty_array_with_capacity(v___x_3407_);
lean_inc_ref(v___x_3408_);
v___x_3409_ = lean_array_push(v___x_3408_, v_name_3392_);
v___x_3410_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_3404_, v___x_3400_, v___x_3409_, v___x_3402_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
lean_dec_ref(v___x_3409_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_options_3411_; lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3452_; 
v_options_3411_ = lean_ctor_get(v_a_3397_, 2);
v_a_3412_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3414_ = v___x_3410_;
v_isShared_3415_ = v_isSharedCheck_3452_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3410_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3452_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v_inheritedTraceOptions_3416_; uint8_t v_hasTrace_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v_inheritedTraceOptions_3416_ = lean_ctor_get(v_a_3397_, 13);
v_hasTrace_3417_ = lean_ctor_get_uint8(v_options_3411_, sizeof(void*)*1);
v___x_3418_ = lean_array_push(v___x_3408_, v_a_3406_);
v___x_3419_ = l_Array_append___redArg(v___x_3418_, v_a_3412_);
lean_dec(v_a_3412_);
if (v_hasTrace_3417_ == 0)
{
lean_object* v___x_3421_; 
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v___x_3419_);
v___x_3421_ = v___x_3414_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3423_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3424_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3);
v___x_3425_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3416_, v_options_3411_, v___x_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3427_; 
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v___x_3419_);
v___x_3427_ = v___x_3414_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3419_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
lean_del_object(v___x_3414_);
v___x_3429_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5);
lean_inc_ref(v___x_3419_);
v___x_3430_ = lean_array_to_list(v___x_3419_);
v___x_3431_ = lean_box(0);
v___x_3432_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(v___x_3430_, v___x_3431_);
v___x_3433_ = l_Lean_MessageData_ofList(v___x_3432_);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3429_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v___x_3423_, v___x_3434_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3442_ == 0)
{
lean_object* v_unused_3443_; 
v_unused_3443_ = lean_ctor_get(v___x_3435_, 0);
lean_dec(v_unused_3443_);
v___x_3437_ = v___x_3435_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_dec(v___x_3435_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3419_);
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3419_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec_ref(v___x_3419_);
v_a_3444_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3435_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3435_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec_ref(v___x_3408_);
lean_dec(v_a_3406_);
v_a_3453_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3410_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3410_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_name_3392_);
v_a_3461_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3403_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3403_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd___boxed(lean_object* v_name_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(v_name_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
lean_dec(v_a_3471_);
lean_dec_ref(v_a_3470_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0(uint8_t v_a_3478_, lean_object* v_declName_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
if (v_a_3478_ == 0)
{
lean_object* v___x_3487_; 
v___x_3487_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(v_declName_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
return v___x_3487_;
}
else
{
lean_object* v___x_3488_; 
v___x_3488_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(v_declName_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0___boxed(lean_object* v_a_3489_, lean_object* v_declName_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
uint8_t v_a_3792__boxed_3498_; lean_object* v_res_3499_; 
v_a_3792__boxed_3498_ = lean_unbox(v_a_3489_);
v_res_3499_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0(v_a_3792__boxed_3498_, v_declName_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
return v_res_3499_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3500_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0);
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
return v___x_3502_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3503_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1);
v___x_3504_ = lean_unsigned_to_nat(0u);
v___x_3505_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
lean_ctor_set(v___x_3505_, 2, v___x_3504_);
lean_ctor_set(v___x_3505_, 3, v___x_3504_);
lean_ctor_set(v___x_3505_, 4, v___x_3503_);
lean_ctor_set(v___x_3505_, 5, v___x_3503_);
lean_ctor_set(v___x_3505_, 6, v___x_3503_);
lean_ctor_set(v___x_3505_, 7, v___x_3503_);
lean_ctor_set(v___x_3505_, 8, v___x_3503_);
lean_ctor_set(v___x_3505_, 9, v___x_3503_);
return v___x_3505_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = lean_unsigned_to_nat(32u);
v___x_3507_ = lean_mk_empty_array_with_capacity(v___x_3506_);
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
return v___x_3508_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3509_ = ((size_t)5ULL);
v___x_3510_ = lean_unsigned_to_nat(0u);
v___x_3511_ = lean_unsigned_to_nat(32u);
v___x_3512_ = lean_mk_empty_array_with_capacity(v___x_3511_);
v___x_3513_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3);
v___x_3514_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
lean_ctor_set(v___x_3514_, 1, v___x_3512_);
lean_ctor_set(v___x_3514_, 2, v___x_3510_);
lean_ctor_set(v___x_3514_, 3, v___x_3510_);
lean_ctor_set_usize(v___x_3514_, 4, v___x_3509_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3515_ = lean_box(1);
v___x_3516_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4);
v___x_3517_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1);
v___x_3518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
lean_ctor_set(v___x_3518_, 1, v___x_3516_);
lean_ctor_set(v___x_3518_, 2, v___x_3515_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_msgData_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3522_; lean_object* v_env_3523_; lean_object* v___x_3524_; lean_object* v_scopes_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v_opts_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3522_ = lean_st_ref_get(v___y_3520_);
v_env_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc_ref(v_env_3523_);
lean_dec(v___x_3522_);
v___x_3524_ = lean_st_ref_get(v___y_3520_);
v_scopes_3525_ = lean_ctor_get(v___x_3524_, 2);
lean_inc(v_scopes_3525_);
lean_dec(v___x_3524_);
v___x_3526_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3527_ = l_List_head_x21___redArg(v___x_3526_, v_scopes_3525_);
lean_dec(v_scopes_3525_);
v_opts_3528_ = lean_ctor_get(v___x_3527_, 1);
lean_inc_ref(v_opts_3528_);
lean_dec(v___x_3527_);
v___x_3529_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2);
v___x_3530_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5);
v___x_3531_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3531_, 0, v_env_3523_);
lean_ctor_set(v___x_3531_, 1, v___x_3529_);
lean_ctor_set(v___x_3531_, 2, v___x_3530_);
lean_ctor_set(v___x_3531_, 3, v_opts_3528_);
v___x_3532_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
lean_ctor_set(v___x_3532_, 1, v_msgData_3519_);
v___x_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___boxed(lean_object* v_msgData_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msgData_3534_, v___y_3535_);
lean_dec(v___y_3535_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msgData_3538_, lean_object* v_macroStack_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v___x_3542_; lean_object* v_scopes_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v_opts_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; uint8_t v___x_3549_; 
v___x_3542_ = lean_st_ref_get(v___y_3540_);
v_scopes_3543_ = lean_ctor_get(v___x_3542_, 2);
lean_inc(v_scopes_3543_);
lean_dec(v___x_3542_);
v___x_3544_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3545_ = l_List_head_x21___redArg(v___x_3544_, v_scopes_3543_);
lean_dec(v_scopes_3543_);
v_opts_3546_ = lean_ctor_get(v___x_3545_, 1);
lean_inc_ref(v_opts_3546_);
lean_dec(v___x_3545_);
v___x_3547_ = l_Lean_Elab_pp_macroStack;
v___x_3548_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_3546_, v___x_3547_);
lean_dec_ref(v_opts_3546_);
v___x_3549_ = lean_bool_not(v___x_3548_);
if (v___x_3549_ == 0)
{
if (lean_obj_tag(v_macroStack_3539_) == 0)
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_msgData_3538_);
return v___x_3550_;
}
else
{
lean_object* v_head_3551_; lean_object* v_after_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3567_; 
v_head_3551_ = lean_ctor_get(v_macroStack_3539_, 0);
lean_inc(v_head_3551_);
v_after_3552_ = lean_ctor_get(v_head_3551_, 1);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_head_3551_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; 
v_unused_3568_ = lean_ctor_get(v_head_3551_, 0);
lean_dec(v_unused_3568_);
v___x_3554_ = v_head_3551_;
v_isShared_3555_ = v_isSharedCheck_3567_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_after_3552_);
lean_dec(v_head_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3567_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3556_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_3555_ == 0)
{
lean_ctor_set_tag(v___x_3554_, 7);
lean_ctor_set(v___x_3554_, 1, v___x_3556_);
lean_ctor_set(v___x_3554_, 0, v_msgData_3538_);
v___x_3558_ = v___x_3554_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_msgData_3538_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v_msgData_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3559_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_3560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3558_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = l_Lean_MessageData_ofSyntax(v_after_3552_);
v___x_3562_ = l_Lean_indentD(v___x_3561_);
v_msgData_3563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3563_, 0, v___x_3560_);
lean_ctor_set(v_msgData_3563_, 1, v___x_3562_);
v___x_3564_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(v_msgData_3563_, v_macroStack_3539_);
v___x_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
return v___x_3565_;
}
}
}
}
else
{
lean_object* v___x_3569_; 
lean_dec(v_macroStack_3539_);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v_msgData_3538_);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msgData_3570_, lean_object* v_macroStack_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_msgData_3570_, v_macroStack_3571_, v___y_3572_);
lean_dec(v___y_3572_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Lean_Elab_Command_getRef___redArg(v___y_3576_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v_macroStack_3581_; lean_object* v___x_3582_; lean_object* v_a_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3594_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3579_, 1);
v_macroStack_3581_ = lean_ctor_get(v___y_3576_, 4);
v___x_3582_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msg_3575_, v___y_3577_);
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref(v___x_3582_);
v___x_3584_ = l_Lean_Elab_getBetterRef(v_a_3580_, v_macroStack_3581_);
lean_dec(v_a_3580_);
lean_inc(v_macroStack_3581_);
v___x_3585_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_a_3583_, v_macroStack_3581_, v___y_3577_);
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3588_ = v___x_3585_;
v_isShared_3589_ = v_isSharedCheck_3594_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3585_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3594_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3584_);
lean_ctor_set(v___x_3590_, 1, v_a_3586_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set_tag(v___x_3588_, 1);
lean_ctor_set(v___x_3588_, 0, v___x_3590_);
v___x_3592_ = v___x_3588_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec_ref(v_msg_3575_);
v_a_3595_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3579_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3579_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3603_, v___y_3604_, v___y_3605_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_3608_, lean_object* v_msg_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_Elab_Command_getRef___redArg(v___y_3610_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v_fileName_3615_; lean_object* v_fileMap_3616_; lean_object* v_currRecDepth_3617_; lean_object* v_cmdPos_3618_; lean_object* v_macroStack_3619_; lean_object* v_quotContext_x3f_3620_; lean_object* v_currMacroScope_3621_; lean_object* v_snap_x3f_3622_; lean_object* v_cancelTk_x3f_3623_; uint8_t v_suppressElabErrors_3624_; lean_object* v_ref_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
v_fileName_3615_ = lean_ctor_get(v___y_3610_, 0);
v_fileMap_3616_ = lean_ctor_get(v___y_3610_, 1);
v_currRecDepth_3617_ = lean_ctor_get(v___y_3610_, 2);
v_cmdPos_3618_ = lean_ctor_get(v___y_3610_, 3);
v_macroStack_3619_ = lean_ctor_get(v___y_3610_, 4);
v_quotContext_x3f_3620_ = lean_ctor_get(v___y_3610_, 5);
v_currMacroScope_3621_ = lean_ctor_get(v___y_3610_, 6);
v_snap_x3f_3622_ = lean_ctor_get(v___y_3610_, 8);
v_cancelTk_x3f_3623_ = lean_ctor_get(v___y_3610_, 9);
v_suppressElabErrors_3624_ = lean_ctor_get_uint8(v___y_3610_, sizeof(void*)*10);
v_ref_3625_ = l_Lean_replaceRef(v_ref_3608_, v_a_3614_);
lean_dec(v_a_3614_);
lean_inc(v_cancelTk_x3f_3623_);
lean_inc(v_snap_x3f_3622_);
lean_inc(v_currMacroScope_3621_);
lean_inc(v_quotContext_x3f_3620_);
lean_inc(v_macroStack_3619_);
lean_inc(v_cmdPos_3618_);
lean_inc(v_currRecDepth_3617_);
lean_inc_ref(v_fileMap_3616_);
lean_inc_ref(v_fileName_3615_);
v___x_3626_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3626_, 0, v_fileName_3615_);
lean_ctor_set(v___x_3626_, 1, v_fileMap_3616_);
lean_ctor_set(v___x_3626_, 2, v_currRecDepth_3617_);
lean_ctor_set(v___x_3626_, 3, v_cmdPos_3618_);
lean_ctor_set(v___x_3626_, 4, v_macroStack_3619_);
lean_ctor_set(v___x_3626_, 5, v_quotContext_x3f_3620_);
lean_ctor_set(v___x_3626_, 6, v_currMacroScope_3621_);
lean_ctor_set(v___x_3626_, 7, v_ref_3625_);
lean_ctor_set(v___x_3626_, 8, v_snap_x3f_3622_);
lean_ctor_set(v___x_3626_, 9, v_cancelTk_x3f_3623_);
lean_ctor_set_uint8(v___x_3626_, sizeof(void*)*10, v_suppressElabErrors_3624_);
v___x_3627_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3609_, v___x_3626_, v___y_3611_);
lean_dec_ref_known(v___x_3626_, 10);
return v___x_3627_;
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v_msg_3609_);
v_a_3628_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3613_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3613_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3636_, lean_object* v_msg_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_3636_, v_msg_3637_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v_ref_3636_);
return v_res_3641_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__0));
v___x_3644_ = l_Lean_stringToMessageData(v___x_3643_);
return v___x_3644_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__2));
v___x_3647_ = l_Lean_stringToMessageData(v___x_3646_);
return v___x_3647_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__4));
v___x_3650_ = l_Lean_stringToMessageData(v___x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_3656_ = l_Lean_stringToMessageData(v___x_3655_);
return v___x_3656_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_3659_ = l_Lean_stringToMessageData(v___x_3658_);
return v___x_3659_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_3662_ = l_Lean_stringToMessageData(v___x_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3663_, lean_object* v_declHint_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v___x_3667_; lean_object* v_env_3668_; uint8_t v___y_3670_; uint8_t v___x_3726_; uint8_t v___x_3727_; 
v___x_3667_ = lean_st_ref_get(v___y_3665_);
v_env_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc_ref(v_env_3668_);
lean_dec(v___x_3667_);
v___x_3726_ = l_Lean_Name_isAnonymous(v_declHint_3664_);
v___x_3727_ = lean_bool_not(v___x_3726_);
if (v___x_3727_ == 0)
{
v___y_3670_ = v___x_3727_;
goto v___jp_3669_;
}
else
{
uint8_t v_isExporting_3728_; 
v_isExporting_3728_ = lean_ctor_get_uint8(v_env_3668_, sizeof(void*)*8);
v___y_3670_ = v_isExporting_3728_;
goto v___jp_3669_;
}
v___jp_3669_:
{
if (v___y_3670_ == 0)
{
lean_object* v___x_3671_; 
lean_dec_ref(v_env_3668_);
lean_dec(v_declHint_3664_);
v___x_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3671_, 0, v_msg_3663_);
return v___x_3671_;
}
else
{
uint8_t v___x_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v___x_3672_ = 0;
lean_inc_ref(v_env_3668_);
v___x_3673_ = l_Lean_Environment_setExporting(v_env_3668_, v___x_3672_);
lean_inc(v_declHint_3664_);
lean_inc_ref(v___x_3673_);
v___x_3674_ = l_Lean_Environment_contains(v___x_3673_, v_declHint_3664_, v___y_3670_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; 
lean_dec_ref(v___x_3673_);
lean_dec_ref(v_env_3668_);
lean_dec(v_declHint_3664_);
v___x_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3675_, 0, v_msg_3663_);
return v___x_3675_;
}
else
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v_c_3681_; lean_object* v___x_3682_; 
v___x_3676_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2);
v___x_3677_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5);
v___x_3678_ = l_Lean_Options_empty;
v___x_3679_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3673_);
lean_ctor_set(v___x_3679_, 1, v___x_3676_);
lean_ctor_set(v___x_3679_, 2, v___x_3677_);
lean_ctor_set(v___x_3679_, 3, v___x_3678_);
lean_inc(v_declHint_3664_);
v___x_3680_ = l_Lean_MessageData_ofConstName(v_declHint_3664_, v___x_3672_);
v_c_3681_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3681_, 0, v___x_3679_);
lean_ctor_set(v_c_3681_, 1, v___x_3680_);
v___x_3682_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3668_, v_declHint_3664_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
lean_dec_ref(v_env_3668_);
lean_dec(v_declHint_3664_);
v___x_3683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3683_);
lean_ctor_set(v___x_3684_, 1, v_c_3681_);
v___x_3685_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3684_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v___x_3687_ = l_Lean_MessageData_note(v___x_3686_);
v___x_3688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3688_, 0, v_msg_3663_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
return v___x_3689_;
}
else
{
lean_object* v_val_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3725_; 
v_val_3690_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3692_ = v___x_3682_;
v_isShared_3693_ = v_isSharedCheck_3725_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_val_3690_);
lean_dec(v___x_3682_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3725_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v_mod_3697_; uint8_t v___x_3698_; 
v___x_3694_ = lean_box(0);
v___x_3695_ = l_Lean_Environment_header(v_env_3668_);
lean_dec_ref(v_env_3668_);
v___x_3696_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3695_);
v_mod_3697_ = lean_array_get(v___x_3694_, v___x_3696_, v_val_3690_);
lean_dec(v_val_3690_);
lean_dec_ref(v___x_3696_);
v___x_3698_ = l_Lean_isPrivateName(v_declHint_3664_);
lean_dec(v_declHint_3664_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3710_; 
v___x_3699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_3700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
lean_ctor_set(v___x_3700_, 1, v_c_3681_);
v___x_3701_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3700_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = l_Lean_MessageData_ofName(v_mod_3697_);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_3706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3704_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = l_Lean_MessageData_note(v___x_3706_);
v___x_3708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3708_, 0, v_msg_3663_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set_tag(v___x_3692_, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3708_);
v___x_3710_ = v___x_3692_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
else
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3712_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v_c_3681_);
v___x_3714_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3713_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = l_Lean_MessageData_ofName(v_mod_3697_);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = l_Lean_MessageData_note(v___x_3719_);
v___x_3721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3721_, 0, v_msg_3663_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set_tag(v___x_3692_, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3721_);
v___x_3723_ = v___x_3692_;
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3729_, lean_object* v_declHint_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3729_, v_declHint_3730_, v___y_3731_);
lean_dec(v___y_3731_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_msg_3734_, lean_object* v_declHint_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3749_; 
v___x_3739_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3734_, v_declHint_3735_, v___y_3737_);
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3742_ = v___x_3739_;
v_isShared_3743_ = v_isSharedCheck_3749_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3749_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
v___x_3744_ = l_Lean_unknownIdentifierMessageTag;
v___x_3745_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
lean_ctor_set(v___x_3745_, 1, v_a_3740_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v___x_3745_);
v___x_3747_ = v___x_3742_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_3750_, lean_object* v_declHint_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3750_, v_declHint_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3756_, lean_object* v_msg_3757_, lean_object* v_declHint_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v___x_3762_; lean_object* v_a_3763_; lean_object* v___x_3764_; 
v___x_3762_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3757_, v_declHint_3758_, v___y_3759_, v___y_3760_);
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref(v___x_3762_);
v___x_3764_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_3756_, v_a_3763_, v___y_3759_, v___y_3760_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3765_, lean_object* v_msg_3766_, lean_object* v_declHint_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3765_, v_msg_3766_, v_declHint_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v_ref_3765_);
return v_res_3771_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__0));
v___x_3774_ = l_Lean_stringToMessageData(v___x_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3775_, lean_object* v_constName_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v___x_3780_; uint8_t v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3780_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_3781_ = 0;
lean_inc(v_constName_3776_);
v___x_3782_ = l_Lean_MessageData_ofConstName(v_constName_3776_, v___x_3781_);
v___x_3783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3780_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v___x_3784_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3775_, v___x_3785_, v_constName_3776_, v___y_3777_, v___y_3778_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3787_, lean_object* v_constName_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3787_, v_constName_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v_ref_3787_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Lean_Elab_Command_getRef___redArg(v___y_3794_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3799_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v___x_3799_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_a_3798_, v_constName_3793_, v___y_3794_, v___y_3795_);
lean_dec(v_a_3798_);
return v___x_3799_;
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec(v_constName_3793_);
v_a_3800_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3797_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3797_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_3808_, v___y_3809_, v___y_3810_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(lean_object* v_constName_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v___x_3817_; lean_object* v_env_3818_; uint8_t v___x_3819_; lean_object* v___x_3820_; 
v___x_3817_ = lean_st_ref_get(v___y_3815_);
v_env_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc_ref(v_env_3818_);
lean_dec(v___x_3817_);
v___x_3819_ = 0;
lean_inc(v_constName_3813_);
v___x_3820_ = l_Lean_Environment_find_x3f(v_env_3818_, v_constName_3813_, v___x_3819_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_3813_, v___y_3814_, v___y_3815_);
return v___x_3821_;
}
else
{
lean_object* v_val_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec(v_constName_3813_);
v_val_3822_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3820_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_val_3822_);
lean_dec(v___x_3820_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set_tag(v___x_3824_, 0);
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_val_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0___boxed(lean_object* v_constName_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_constName_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(lean_object* v_x_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
if (lean_obj_tag(v_x_3835_) == 0)
{
uint8_t v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = 1;
v___x_3840_ = lean_box(v___x_3839_);
v___x_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
return v___x_3841_;
}
else
{
lean_object* v_head_3842_; lean_object* v_tail_3843_; lean_object* v___x_3844_; 
v_head_3842_ = lean_ctor_get(v_x_3835_, 0);
lean_inc(v_head_3842_);
v_tail_3843_ = lean_ctor_get(v_x_3835_, 1);
lean_inc(v_tail_3843_);
lean_dec_ref_known(v_x_3835_, 2);
v___x_3844_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_head_3842_, v___y_3836_, v___y_3837_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3863_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3847_ = v___x_3844_;
v_isShared_3848_ = v_isSharedCheck_3863_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3844_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3863_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
if (lean_obj_tag(v_a_3845_) == 6)
{
lean_object* v_val_3849_; lean_object* v_numFields_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; 
v_val_3849_ = lean_ctor_get(v_a_3845_, 0);
lean_inc_ref(v_val_3849_);
lean_dec_ref_known(v_a_3845_, 1);
v_numFields_3850_ = lean_ctor_get(v_val_3849_, 4);
lean_inc(v_numFields_3850_);
lean_dec_ref(v_val_3849_);
v___x_3851_ = lean_unsigned_to_nat(0u);
v___x_3852_ = lean_nat_dec_eq(v_numFields_3850_, v___x_3851_);
lean_dec(v_numFields_3850_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3855_; 
lean_dec(v_tail_3843_);
v___x_3853_ = lean_box(v___x_3852_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v___x_3853_);
v___x_3855_ = v___x_3847_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
else
{
lean_del_object(v___x_3847_);
v_x_3835_ = v_tail_3843_;
goto _start;
}
}
else
{
uint8_t v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3861_; 
lean_dec(v_a_3845_);
lean_dec(v_tail_3843_);
v___x_3858_ = 0;
v___x_3859_ = lean_box(v___x_3858_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v___x_3859_);
v___x_3861_ = v___x_3847_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_dec(v_tail_3843_);
v_a_3864_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3844_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3844_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1___boxed(lean_object* v_x_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(v_x_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(lean_object* v_declName_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_declName_3877_, v___y_3878_, v___y_3879_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3938_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3938_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3938_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
if (lean_obj_tag(v_a_3882_) == 5)
{
lean_object* v_val_3886_; lean_object* v_toConstantVal_3887_; lean_object* v_numParams_3888_; lean_object* v_numIndices_3889_; lean_object* v_ctors_3890_; uint8_t v_isRec_3891_; uint8_t v_isUnsafe_3892_; uint8_t v___y_3894_; lean_object* v_type_3927_; uint8_t v___x_3928_; uint8_t v___x_3929_; 
v_val_3886_ = lean_ctor_get(v_a_3882_, 0);
lean_inc_ref(v_val_3886_);
lean_dec_ref_known(v_a_3882_, 1);
v_toConstantVal_3887_ = lean_ctor_get(v_val_3886_, 0);
v_numParams_3888_ = lean_ctor_get(v_val_3886_, 1);
lean_inc(v_numParams_3888_);
v_numIndices_3889_ = lean_ctor_get(v_val_3886_, 2);
lean_inc(v_numIndices_3889_);
v_ctors_3890_ = lean_ctor_get(v_val_3886_, 4);
lean_inc(v_ctors_3890_);
v_isRec_3891_ = lean_ctor_get_uint8(v_val_3886_, sizeof(void*)*6);
v_isUnsafe_3892_ = lean_ctor_get_uint8(v_val_3886_, sizeof(void*)*6 + 1);
v_type_3927_ = lean_ctor_get(v_toConstantVal_3887_, 2);
v___x_3928_ = l_Lean_Expr_isProp(v_type_3927_);
v___x_3929_ = lean_bool_not(v___x_3928_);
if (v___x_3929_ == 0)
{
lean_dec_ref(v_val_3886_);
v___y_3894_ = v___x_3929_;
goto v___jp_3893_;
}
else
{
lean_object* v___x_3930_; lean_object* v___x_3931_; uint8_t v___x_3932_; 
v___x_3930_ = l_Lean_InductiveVal_numTypeFormers(v_val_3886_);
lean_dec_ref(v_val_3886_);
v___x_3931_ = lean_unsigned_to_nat(1u);
v___x_3932_ = lean_nat_dec_eq(v___x_3930_, v___x_3931_);
lean_dec(v___x_3930_);
v___y_3894_ = v___x_3932_;
goto v___jp_3893_;
}
v___jp_3893_:
{
if (v___y_3894_ == 0)
{
lean_object* v___x_3895_; lean_object* v___x_3897_; 
lean_dec(v_ctors_3890_);
lean_dec(v_numIndices_3889_);
lean_dec(v_numParams_3888_);
v___x_3895_ = lean_box(v___y_3894_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3895_);
v___x_3897_ = v___x_3884_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
else
{
lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3899_ = lean_unsigned_to_nat(0u);
v___x_3900_ = lean_nat_dec_eq(v_numIndices_3889_, v___x_3899_);
lean_dec(v_numIndices_3889_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
lean_dec(v_ctors_3890_);
lean_dec(v_numParams_3888_);
v___x_3901_ = lean_box(v___x_3900_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3901_);
v___x_3903_ = v___x_3884_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3901_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
else
{
uint8_t v___x_3905_; 
v___x_3905_ = lean_nat_dec_eq(v_numParams_3888_, v___x_3899_);
lean_dec(v_numParams_3888_);
if (v___x_3905_ == 0)
{
lean_object* v___x_3906_; lean_object* v___x_3908_; 
lean_dec(v_ctors_3890_);
v___x_3906_ = lean_box(v___x_3905_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3906_);
v___x_3908_ = v___x_3884_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
else
{
uint8_t v___x_3910_; uint8_t v___x_3911_; 
v___x_3910_ = l_List_isEmpty___redArg(v_ctors_3890_);
v___x_3911_ = lean_bool_not(v___x_3910_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; lean_object* v___x_3914_; 
lean_dec(v_ctors_3890_);
v___x_3912_ = lean_box(v___x_3911_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3912_);
v___x_3914_ = v___x_3884_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
else
{
uint8_t v___x_3916_; 
v___x_3916_ = lean_bool_not(v_isRec_3891_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
lean_dec(v_ctors_3890_);
v___x_3917_ = lean_box(v___x_3916_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3917_);
v___x_3919_ = v___x_3884_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
else
{
uint8_t v___x_3921_; 
v___x_3921_ = lean_bool_not(v_isUnsafe_3892_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3924_; 
lean_dec(v_ctors_3890_);
v___x_3922_ = lean_box(v___x_3921_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3922_);
v___x_3924_ = v___x_3884_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
else
{
lean_object* v___x_3926_; 
lean_del_object(v___x_3884_);
v___x_3926_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(v_ctors_3890_, v___y_3878_, v___y_3879_);
return v___x_3926_;
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
uint8_t v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3936_; 
lean_dec(v_a_3882_);
v___x_3933_ = 0;
v___x_3934_ = lean_box(v___x_3933_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3934_);
v___x_3936_ = v___x_3884_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3934_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
v_a_3939_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3881_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3881_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0___boxed(lean_object* v_declName_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(v_declName_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(lean_object* v_as_3952_, size_t v_i_3953_, size_t v_stop_3954_, lean_object* v_b_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
uint8_t v___x_3959_; 
v___x_3959_ = lean_usize_dec_eq(v_i_3953_, v_stop_3954_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = lean_array_uget_borrowed(v_as_3952_, v_i_3953_);
lean_inc(v___x_3960_);
v___x_3961_ = l_Lean_Elab_Command_elabCommand(v___x_3960_, v___y_3956_, v___y_3957_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; size_t v___x_3963_; size_t v___x_3964_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3961_, 1);
v___x_3963_ = ((size_t)1ULL);
v___x_3964_ = lean_usize_add(v_i_3953_, v___x_3963_);
v_i_3953_ = v___x_3964_;
v_b_3955_ = v_a_3962_;
goto _start;
}
else
{
return v___x_3961_;
}
}
else
{
lean_object* v___x_3966_; 
v___x_3966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3966_, 0, v_b_3955_);
return v___x_3966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1___boxed(lean_object* v_as_3967_, lean_object* v_i_3968_, lean_object* v_stop_3969_, lean_object* v_b_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
size_t v_i_boxed_3974_; size_t v_stop_boxed_3975_; lean_object* v_res_3976_; 
v_i_boxed_3974_ = lean_unbox_usize(v_i_3968_);
lean_dec(v_i_3968_);
v_stop_boxed_3975_ = lean_unbox_usize(v_stop_3969_);
lean_dec(v_stop_3969_);
v_res_3976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_as_3967_, v_i_boxed_3974_, v_stop_boxed_3975_, v_b_3970_, v___y_3971_, v___y_3972_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec_ref(v_as_3967_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1(lean_object* v_declName_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v___x_3981_; 
lean_inc(v_declName_3977_);
v___x_3981_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(v_declName_3977_, v___y_3978_, v___y_3979_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___y_3983_; lean_object* v___x_3984_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3981_, 1);
v___y_3983_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___y_3983_, 0, v_a_3982_);
lean_closure_set(v___y_3983_, 1, v_declName_3977_);
v___x_3984_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_3983_, v___y_3978_, v___y_3979_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_4006_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3987_ = v___x_3984_;
v_isShared_3988_ = v_isSharedCheck_4006_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3984_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_4006_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v___x_3989_ = lean_unsigned_to_nat(0u);
v___x_3990_ = lean_array_get_size(v_a_3985_);
v___x_3991_ = lean_box(0);
v___x_3992_ = lean_nat_dec_lt(v___x_3989_, v___x_3990_);
if (v___x_3992_ == 0)
{
lean_object* v___x_3994_; 
lean_dec(v_a_3985_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3991_);
v___x_3994_ = v___x_3987_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3991_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
else
{
uint8_t v___x_3996_; 
v___x_3996_ = lean_nat_dec_le(v___x_3990_, v___x_3990_);
if (v___x_3996_ == 0)
{
if (v___x_3992_ == 0)
{
lean_object* v___x_3998_; 
lean_dec(v_a_3985_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3991_);
v___x_3998_ = v___x_3987_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3991_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
else
{
size_t v___x_4000_; size_t v___x_4001_; lean_object* v___x_4002_; 
lean_del_object(v___x_3987_);
v___x_4000_ = ((size_t)0ULL);
v___x_4001_ = lean_usize_of_nat(v___x_3990_);
v___x_4002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_a_3985_, v___x_4000_, v___x_4001_, v___x_3991_, v___y_3978_, v___y_3979_);
lean_dec(v_a_3985_);
return v___x_4002_;
}
}
else
{
size_t v___x_4003_; size_t v___x_4004_; lean_object* v___x_4005_; 
lean_del_object(v___x_3987_);
v___x_4003_ = ((size_t)0ULL);
v___x_4004_ = lean_usize_of_nat(v___x_3990_);
v___x_4005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_a_3985_, v___x_4003_, v___x_4004_, v___x_3991_, v___y_3978_, v___y_3979_);
lean_dec(v_a_3985_);
return v___x_4005_;
}
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
v_a_4007_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3984_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3984_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec(v_declName_3977_);
v_a_4015_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_3981_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_3981_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1___boxed(lean_object* v_declName_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1(v_declName_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(lean_object* v_declName_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v___f_4032_; lean_object* v___x_4033_; 
lean_inc(v_declName_4028_);
v___f_4032_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_4032_, 0, v_declName_4028_);
v___x_4033_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_4028_, v___f_4032_, v_a_4029_, v_a_4030_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___boxed(lean_object* v_declName_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(v_declName_4034_, v_a_4035_, v_a_4036_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4039_, lean_object* v_constName_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_4040_, v___y_4041_, v___y_4042_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4045_, lean_object* v_constName_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1(v_00_u03b1_4045_, v_constName_4046_, v___y_4047_, v___y_4048_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4051_, lean_object* v_ref_4052_, lean_object* v_constName_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4052_, v_constName_4053_, v___y_4054_, v___y_4055_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4058_, lean_object* v_ref_4059_, lean_object* v_constName_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4058_, v_ref_4059_, v_constName_4060_, v___y_4061_, v___y_4062_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v_ref_4059_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_4065_, lean_object* v_ref_4066_, lean_object* v_msg_4067_, lean_object* v_declHint_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4066_, v_msg_4067_, v_declHint_4068_, v___y_4069_, v___y_4070_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4073_, lean_object* v_ref_4074_, lean_object* v_msg_4075_, lean_object* v_declHint_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_4073_, v_ref_4074_, v_msg_4075_, v_declHint_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v_ref_4074_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_4081_, lean_object* v_declHint_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_4081_, v_declHint_4082_, v___y_4084_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_4087_, lean_object* v_declHint_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7(v_msg_4087_, v_declHint_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_4093_, lean_object* v_ref_4094_, lean_object* v_msg_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_4094_, v_msg_4095_, v___y_4096_, v___y_4097_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_4100_, lean_object* v_ref_4101_, lean_object* v_msg_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(v_00_u03b1_4100_, v_ref_4101_, v_msg_4102_, v___y_4103_, v___y_4104_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v_ref_4101_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_msgData_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msgData_4107_, v___y_4109_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___boxed(lean_object* v_msgData_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10(v_msgData_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_4117_, lean_object* v_msg_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_4118_, v___y_4119_, v___y_4120_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4123_, lean_object* v_msg_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_4123_, v_msg_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11(lean_object* v_msgData_4129_, lean_object* v_macroStack_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_msgData_4129_, v_macroStack_4130_, v___y_4132_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_msgData_4135_, lean_object* v_macroStack_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11(v_msgData_4135_, v_macroStack_4136_, v___y_4137_, v___y_4138_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(lean_object* v_declName_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v___x_4144_; lean_object* v_env_4145_; uint8_t v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4144_ = lean_st_ref_get(v___y_4142_);
v_env_4145_ = lean_ctor_get(v___x_4144_, 0);
lean_inc_ref(v_env_4145_);
lean_dec(v___x_4144_);
v___x_4146_ = l_Lean_isInductiveCore(v_env_4145_, v_declName_4141_);
v___x_4147_ = lean_box(v___x_4146_);
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v_declName_4149_, v___y_4150_);
lean_dec(v___y_4150_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1(lean_object* v_declName_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v___x_4157_; 
v___x_4157_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v_declName_4153_, v___y_4155_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___boxed(lean_object* v_declName_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1(v_declName_4158_, v___y_4159_, v___y_4160_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(uint8_t v_____do__lift_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
uint8_t v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4167_ = lean_bool_not(v_____do__lift_4163_);
v___x_4168_ = lean_box(v___x_4167_);
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
uint8_t v_____do__lift_1670__boxed_4174_; lean_object* v_res_4175_; 
v_____do__lift_1670__boxed_4174_ = lean_unbox(v_____do__lift_4170_);
v_res_4175_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v_____do__lift_1670__boxed_4174_, v___y_4171_, v___y_4172_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(lean_object* v_as_4176_, size_t v_i_4177_, size_t v_stop_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
uint8_t v___x_4182_; 
v___x_4182_ = lean_usize_dec_eq(v_i_4177_, v_stop_4178_);
if (v___x_4182_ == 0)
{
uint8_t v___x_4183_; uint8_t v_a_4185_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4183_ = 1;
v___x_4191_ = lean_array_uget_borrowed(v_as_4176_, v_i_4177_);
lean_inc(v___x_4191_);
v___x_4192_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v___x_4191_, v___y_4180_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; uint8_t v___x_4194_; uint8_t v___x_4195_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4192_, 1);
v___x_4194_ = lean_unbox(v_a_4193_);
lean_dec(v_a_4193_);
v___x_4195_ = lean_bool_not(v___x_4194_);
v_a_4185_ = v___x_4195_;
goto v___jp_4184_;
}
else
{
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4196_; uint8_t v___x_4197_; 
v_a_4196_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_a_4196_);
lean_dec_ref_known(v___x_4192_, 1);
v___x_4197_ = lean_unbox(v_a_4196_);
lean_dec(v_a_4196_);
v_a_4185_ = v___x_4197_;
goto v___jp_4184_;
}
else
{
return v___x_4192_;
}
}
v___jp_4184_:
{
if (v_a_4185_ == 0)
{
size_t v___x_4186_; size_t v___x_4187_; 
v___x_4186_ = ((size_t)1ULL);
v___x_4187_ = lean_usize_add(v_i_4177_, v___x_4186_);
v_i_4177_ = v___x_4187_;
goto _start;
}
else
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = lean_box(v___x_4183_);
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
return v___x_4190_;
}
}
}
else
{
uint8_t v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4198_ = 0;
v___x_4199_ = lean_box(v___x_4198_);
v___x_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
return v___x_4200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2___boxed(lean_object* v_as_4201_, lean_object* v_i_4202_, lean_object* v_stop_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
size_t v_i_boxed_4207_; size_t v_stop_boxed_4208_; lean_object* v_res_4209_; 
v_i_boxed_4207_ = lean_unbox_usize(v_i_4202_);
lean_dec(v_i_4202_);
v_stop_boxed_4208_ = lean_unbox_usize(v_stop_4203_);
lean_dec(v_stop_4203_);
v_res_4209_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(v_as_4201_, v_i_boxed_4207_, v_stop_boxed_4208_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v_as_4201_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(lean_object* v_as_4210_, size_t v_sz_4211_, size_t v_i_4212_, lean_object* v_b_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
uint8_t v___x_4217_; 
v___x_4217_ = lean_usize_dec_lt(v_i_4212_, v_sz_4211_);
if (v___x_4217_ == 0)
{
lean_object* v___x_4218_; 
v___x_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4218_, 0, v_b_4213_);
return v___x_4218_;
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4220_; 
v_a_4219_ = lean_array_uget_borrowed(v_as_4210_, v_i_4212_);
lean_inc(v_a_4219_);
v___x_4220_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(v_a_4219_, v___y_4214_, v___y_4215_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v___x_4221_; size_t v___x_4222_; size_t v___x_4223_; 
lean_dec_ref_known(v___x_4220_, 1);
v___x_4221_ = lean_box(0);
v___x_4222_ = ((size_t)1ULL);
v___x_4223_ = lean_usize_add(v_i_4212_, v___x_4222_);
v_i_4212_ = v___x_4223_;
v_b_4213_ = v___x_4221_;
goto _start;
}
else
{
return v___x_4220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0___boxed(lean_object* v_as_4225_, lean_object* v_sz_4226_, lean_object* v_i_4227_, lean_object* v_b_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
size_t v_sz_boxed_4232_; size_t v_i_boxed_4233_; lean_object* v_res_4234_; 
v_sz_boxed_4232_ = lean_unbox_usize(v_sz_4226_);
lean_dec(v_sz_4226_);
v_i_boxed_4233_ = lean_unbox_usize(v_i_4227_);
lean_dec(v_i_4227_);
v_res_4234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(v_as_4225_, v_sz_boxed_4232_, v_i_boxed_4233_, v_b_4228_, v___y_4229_, v___y_4230_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec_ref(v_as_4225_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(lean_object* v_declNames_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_){
_start:
{
uint8_t v_a_4240_; lean_object* v___y_4265_; lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v___x_4268_ = lean_unsigned_to_nat(0u);
v___x_4269_ = lean_array_get_size(v_declNames_4235_);
v___x_4270_ = lean_nat_dec_lt(v___x_4268_, v___x_4269_);
if (v___x_4270_ == 0)
{
lean_object* v___x_4271_; 
v___x_4271_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v___x_4270_, v_a_4236_, v_a_4237_);
v___y_4265_ = v___x_4271_;
goto v___jp_4264_;
}
else
{
if (v___x_4270_ == 0)
{
uint8_t v___x_4272_; 
v___x_4272_ = lean_bool_not(v___x_4270_);
v_a_4240_ = v___x_4272_;
goto v___jp_4239_;
}
else
{
size_t v___x_4273_; size_t v___x_4274_; lean_object* v___x_4275_; 
v___x_4273_ = ((size_t)0ULL);
v___x_4274_ = lean_usize_of_nat(v___x_4269_);
v___x_4275_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(v_declNames_4235_, v___x_4273_, v___x_4274_, v_a_4236_, v_a_4237_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; uint8_t v___x_4277_; lean_object* v___x_4278_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref_known(v___x_4275_, 1);
v___x_4277_ = lean_unbox(v_a_4276_);
lean_dec(v_a_4276_);
v___x_4278_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v___x_4277_, v_a_4236_, v_a_4237_);
v___y_4265_ = v___x_4278_;
goto v___jp_4264_;
}
else
{
v___y_4265_ = v___x_4275_;
goto v___jp_4264_;
}
}
}
v___jp_4239_:
{
if (v_a_4240_ == 0)
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4241_ = lean_box(v_a_4240_);
v___x_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
return v___x_4242_;
}
else
{
lean_object* v___x_4243_; size_t v_sz_4244_; size_t v___x_4245_; lean_object* v___x_4246_; 
v___x_4243_ = lean_box(0);
v_sz_4244_ = lean_array_size(v_declNames_4235_);
v___x_4245_ = ((size_t)0ULL);
v___x_4246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(v_declNames_4235_, v_sz_4244_, v___x_4245_, v___x_4243_, v_a_4236_, v_a_4237_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4254_; 
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4254_ == 0)
{
lean_object* v_unused_4255_; 
v_unused_4255_ = lean_ctor_get(v___x_4246_, 0);
lean_dec(v_unused_4255_);
v___x_4248_ = v___x_4246_;
v_isShared_4249_ = v_isSharedCheck_4254_;
goto v_resetjp_4247_;
}
else
{
lean_dec(v___x_4246_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4254_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4250_; lean_object* v___x_4252_; 
v___x_4250_ = lean_box(v_a_4240_);
if (v_isShared_4249_ == 0)
{
lean_ctor_set(v___x_4248_, 0, v___x_4250_);
v___x_4252_ = v___x_4248_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4250_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
v_a_4256_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4246_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4246_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
v___jp_4264_:
{
if (lean_obj_tag(v___y_4265_) == 0)
{
lean_object* v_a_4266_; uint8_t v___x_4267_; 
v_a_4266_ = lean_ctor_get(v___y_4265_, 0);
lean_inc(v_a_4266_);
lean_dec_ref_known(v___y_4265_, 1);
v___x_4267_ = lean_unbox(v_a_4266_);
lean_dec(v_a_4266_);
v_a_4240_ = v___x_4267_;
goto v___jp_4239_;
}
else
{
return v___y_4265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___boxed(lean_object* v_declNames_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(v_declNames_4279_, v_a_4280_, v_a_4281_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec_ref(v_declNames_4279_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4332_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_4333_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_));
v___x_4334_ = l_Lean_Elab_registerDerivingHandler(v___x_4332_, v___x_4333_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v___x_4335_; uint8_t v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
lean_dec_ref_known(v___x_4334_, 1);
v___x_4335_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_4336_ = 0;
v___x_4337_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_));
v___x_4338_ = l_Lean_registerTraceClass(v___x_4335_, v___x_4336_, v___x_4337_);
return v___x_4338_;
}
else
{
return v___x_4334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2____boxed(lean_object* v_a_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_();
return v_res_4340_;
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
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Ord(uint8_t builtin) {
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
res = l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Deriving_Ord_0__deriving_ord_linear__construction__threshold = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__deriving_ord_linear__construction__threshold);
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_Ord(uint8_t builtin) {
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
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Ord(uint8_t builtin) {
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
res = runtime_initialize_Lean_Elab_Deriving_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_Ord(builtin);
}
#ifdef __cplusplus
}
#endif
