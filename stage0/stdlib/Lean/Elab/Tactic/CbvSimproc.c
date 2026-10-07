// Lean compiler output
// Module: Lean.Elab.Tactic.CbvSimproc
// Imports: public import Init.CbvSimproc public import Lean.Meta.Tactic.Cbv.CbvSimproc public import Lean.Elab.Command
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_Sym_mkPatternFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_elabCbvSimprocPattern___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocPattern___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocPattern___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocPattern___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_elabCbvSimprocPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_elabCbvSimprocPattern___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabCbvSimprocPattern___closed__0 = (const lean_object*)&l_Lean_Elab_elabCbvSimprocPattern___closed__0_value;
static const lean_array_object l_Lean_Elab_elabCbvSimprocPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_elabCbvSimprocPattern___closed__1 = (const lean_object*)&l_Lean_Elab_elabCbvSimprocPattern___closed__1_value;
static const lean_ctor_object l_Lean_Elab_elabCbvSimprocPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabCbvSimprocPattern___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabCbvSimprocPattern___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_elabCbvSimprocPattern___closed__2 = (const lean_object*)&l_Lean_Elab_elabCbvSimprocPattern___closed__2_value;
static const lean_ctor_object l_Lean_Elab_elabCbvSimprocPattern___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_elabCbvSimprocPattern___closed__3 = (const lean_object*)&l_Lean_Elab_elabCbvSimprocPattern___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkSimprocPatternFromExpr___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkSimprocPatternFromExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_mkSimprocPatternFromExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_mkSimprocPatternFromExpr___lam__0___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Elab_mkSimprocPatternFromExpr___closed__0 = (const lean_object*)&l_Lean_Elab_mkSimprocPatternFromExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_mkSimprocPatternFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkSimprocPatternFromExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkCbvSimprocType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Unexpected type for cbv simproc pattern: Expected `"};
static const lean_object* l_Lean_Elab_checkCbvSimprocType___closed__0 = (const lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkCbvSimprocType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkCbvSimprocType___closed__1;
static const lean_string_object l_Lean_Elab_checkCbvSimprocType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_checkCbvSimprocType___closed__2 = (const lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value;
static const lean_string_object l_Lean_Elab_checkCbvSimprocType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_checkCbvSimprocType___closed__3 = (const lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__3_value;
static const lean_string_object l_Lean_Elab_checkCbvSimprocType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Elab_checkCbvSimprocType___closed__4 = (const lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__4_value;
static const lean_string_object l_Lean_Elab_checkCbvSimprocType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Elab_checkCbvSimprocType___closed__5 = (const lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__5_value;
static const lean_string_object l_Lean_Elab_checkCbvSimprocType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l_Lean_Elab_checkCbvSimprocType___closed__6 = (const lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__6_value;
static const lean_ctor_object l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_ctor_object l_Lean_Elab_checkCbvSimprocType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_3),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(243, 37, 220, 98, 36, 118, 162, 63)}};
static const lean_object* l_Lean_Elab_checkCbvSimprocType___closed__7 = (const lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__7_value;
static lean_once_cell_t l_Lean_Elab_checkCbvSimprocType___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkCbvSimprocType___closed__8;
static lean_once_cell_t l_Lean_Elab_checkCbvSimprocType___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkCbvSimprocType___closed__9;
static const lean_string_object l_Lean_Elab_checkCbvSimprocType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "`, but `"};
static const lean_object* l_Lean_Elab_checkCbvSimprocType___closed__10 = (const lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__10_value;
static lean_once_cell_t l_Lean_Elab_checkCbvSimprocType___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkCbvSimprocType___closed__11;
static lean_once_cell_t l_Lean_Elab_checkCbvSimprocType___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkCbvSimprocType___closed__12;
static const lean_string_object l_Lean_Elab_checkCbvSimprocType___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_Elab_checkCbvSimprocType___closed__13 = (const lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__13_value;
static lean_once_cell_t l_Lean_Elab_checkCbvSimprocType___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkCbvSimprocType___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_checkCbvSimprocType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkCbvSimprocType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "cbvSimprocPattern"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 75, 142, 45, 135, 67, 101, 69)}};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabCbvSimprocPattern"};
static const lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(175, 41, 227, 90, 200, 136, 150, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DiscrTree"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Key"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "star"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(8, 3, 45, 254, 183, 37, 206, 62)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "other"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(138, 126, 131, 170, 147, 7, 98, 166)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lit"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(202, 151, 84, 78, 164, 133, 51, 209)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Literal"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natVal"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(39, 22, 220, 12, 129, 114, 43, 97)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(64, 199, 201, 37, 137, 51, 1, 129)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strVal"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(39, 22, 220, 12, 129, 114, 43, 97)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(68, 214, 249, 146, 84, 160, 212, 27)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fvar"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(191, 195, 92, 248, 246, 94, 216, 42)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "FVarId"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(134, 80, 170, 214, 218, 146, 55, 86)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(246, 212, 153, 136, 172, 214, 179, 96)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_0),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(146, 102, 128, 62, 226, 52, 61, 241)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_0),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value),LEAN_SCALAR_PTR_LITERAL(89, 115, 112, 17, 35, 166, 93, 117)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value),LEAN_SCALAR_PTR_LITERAL(96, 241, 3, 72, 213, 31, 49, 170)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "registerBuiltinCbvSimproc"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7;
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10;
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13;
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declare"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(12, 217, 76, 92, 115, 157, 174, 191)}};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "cbvSimprocPatternBuiltin"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 134, 28, 30, 122, 199, 7, 31)}};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "elabCbvSimprocPatternBuiltin"};
static const lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkCbvSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 94, 198, 121, 208, 4, 117, 124)}};
static const lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_elabCbvSimprocPattern___lam__0(lean_object* v_x_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocPattern___lam__0___boxed(lean_object* v_x_3_){
_start:
{
uint8_t v_res_4_; lean_object* v_r_5_; 
v_res_4_ = l_Lean_Elab_elabCbvSimprocPattern___lam__0(v_x_3_);
lean_dec(v_x_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocPattern___lam__1(lean_object* v_stx_6_, lean_object* v___x_7_, uint8_t v___x_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_Term_elabTerm(v_stx_6_, v___x_7_, v___x_8_, v___x_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v_a_17_; uint8_t v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; 
v_a_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc(v_a_17_);
lean_dec_ref_known(v___x_16_, 1);
v___x_18_ = 0;
v___x_19_ = 0;
v___x_20_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_18_, v___x_19_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_27_ == 0)
{
lean_object* v_unused_28_; 
v_unused_28_ = lean_ctor_get(v___x_20_, 0);
lean_dec(v_unused_28_);
v___x_22_ = v___x_20_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_dec(v___x_20_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v_a_17_);
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_17_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
else
{
lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_36_; 
lean_dec(v_a_17_);
v_a_29_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_36_ == 0)
{
v___x_31_ = v___x_20_;
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_dec(v___x_20_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_34_; 
if (v_isShared_32_ == 0)
{
v___x_34_ = v___x_31_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_a_29_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
else
{
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocPattern___lam__1___boxed(lean_object* v_stx_37_, lean_object* v___x_38_, lean_object* v___x_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
uint8_t v___x_357__boxed_47_; lean_object* v_res_48_; 
v___x_357__boxed_47_ = lean_unbox(v___x_39_);
v_res_48_ = l_Lean_Elab_elabCbvSimprocPattern___lam__1(v_stx_37_, v___x_38_, v___x_357__boxed_47_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocPattern(lean_object* v_stx_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v_go_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_69_ = lean_box(0);
v___x_70_ = 1;
v___x_71_ = lean_box(v___x_70_);
v_go_72_ = lean_alloc_closure((void*)(l_Lean_Elab_elabCbvSimprocPattern___lam__1___boxed), 10, 3);
lean_closure_set(v_go_72_, 0, v_stx_63_);
lean_closure_set(v_go_72_, 1, v___x_69_);
lean_closure_set(v_go_72_, 2, v___x_71_);
v___x_73_ = ((lean_object*)(l_Lean_Elab_elabCbvSimprocPattern___closed__2));
v___x_74_ = ((lean_object*)(l_Lean_Elab_elabCbvSimprocPattern___closed__3));
v___x_75_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_go_72_, v___x_73_, v___x_74_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_84_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v_fst_80_; lean_object* v___x_82_; 
v_fst_80_ = lean_ctor_get(v_a_76_, 0);
lean_inc(v_fst_80_);
lean_dec(v_a_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v_fst_80_);
v___x_82_ = v___x_78_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_fst_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
else
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
v_a_85_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v___x_75_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_75_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_a_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocPattern___boxed(lean_object* v_stx_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Elab_elabCbvSimprocPattern(v_stx_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0(lean_object* v_k_100_, lean_object* v_b_101_, lean_object* v_c_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; 
lean_inc(v___y_106_);
lean_inc_ref(v___y_105_);
lean_inc(v___y_104_);
lean_inc_ref(v___y_103_);
v___x_108_ = lean_apply_7(v_k_100_, v_b_101_, v_c_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, lean_box(0));
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0___boxed(lean_object* v_k_109_, lean_object* v_b_110_, lean_object* v_c_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0(v_k_109_, v_b_110_, v_c_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(lean_object* v_e_118_, lean_object* v_k_119_, uint8_t v_cleanupAnnotations_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___f_126_; uint8_t v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___f_126_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_126_, 0, v_k_119_);
v___x_127_ = 1;
v___x_128_ = 0;
v___x_129_ = lean_box(0);
v___x_130_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_118_, v___x_127_, v___x_128_, v___x_127_, v___x_128_, v___x_129_, v___f_126_, v_cleanupAnnotations_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_130_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_130_);
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
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___boxed(lean_object* v_e_147_, lean_object* v_k_148_, lean_object* v_cleanupAnnotations_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_155_; lean_object* v_res_156_; 
v_cleanupAnnotations_boxed_155_ = lean_unbox(v_cleanupAnnotations_149_);
v_res_156_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(v_e_147_, v_k_148_, v_cleanupAnnotations_boxed_155_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0(lean_object* v_00_u03b1_157_, lean_object* v_e_158_, lean_object* v_k_159_, uint8_t v_cleanupAnnotations_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(v_e_158_, v_k_159_, v_cleanupAnnotations_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___boxed(lean_object* v_00_u03b1_167_, lean_object* v_e_168_, lean_object* v_k_169_, lean_object* v_cleanupAnnotations_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_176_; lean_object* v_res_177_; 
v_cleanupAnnotations_boxed_176_ = lean_unbox(v_cleanupAnnotations_170_);
v_res_177_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0(v_00_u03b1_167_, v_e_168_, v_k_169_, v_cleanupAnnotations_boxed_176_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkSimprocPatternFromExpr___lam__0(uint8_t v___x_178_, lean_object* v_args_179_, lean_object* v_body_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
uint8_t v___x_186_; uint8_t v___x_187_; lean_object* v___x_188_; 
v___x_186_ = 0;
v___x_187_ = 1;
v___x_188_ = l_Lean_Meta_mkForallFVars(v_args_179_, v_body_180_, v___x_186_, v___x_178_, v___x_178_, v___x_187_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkSimprocPatternFromExpr___lam__0___boxed(lean_object* v___x_189_, lean_object* v_args_190_, lean_object* v_body_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
uint8_t v___x_637__boxed_197_; lean_object* v_res_198_; 
v___x_637__boxed_197_ = lean_unbox(v___x_189_);
v_res_198_ = l_Lean_Elab_mkSimprocPatternFromExpr___lam__0(v___x_637__boxed_197_, v_args_190_, v_body_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec_ref(v_args_190_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkSimprocPatternFromExpr(lean_object* v_e_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
uint8_t v___x_208_; lean_object* v___f_209_; lean_object* v___x_210_; 
v___x_208_ = 1;
v___f_209_ = ((lean_object*)(l_Lean_Elab_mkSimprocPatternFromExpr___closed__0));
v___x_210_ = l_Lean_Meta_abstractMVars(v_e_202_, v___x_208_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v_paramNames_212_; lean_object* v_expr_213_; uint8_t v___x_214_; lean_object* v___x_215_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
v_paramNames_212_ = lean_ctor_get(v_a_211_, 0);
lean_inc_ref(v_paramNames_212_);
v_expr_213_ = lean_ctor_get(v_a_211_, 2);
lean_inc_ref(v_expr_213_);
lean_dec(v_a_211_);
v___x_214_ = 0;
v___x_215_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(v_expr_213_, v___f_209_, v___x_214_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_215_, 1);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v_a_216_);
v___x_218_ = 0;
v___x_219_ = lean_box(0);
v___x_220_ = l_Lean_Meta_mkFreshExprMVar(v___x_217_, v___x_218_, v___x_219_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
v___x_222_ = lean_array_to_list(v_paramNames_212_);
v___x_223_ = lean_box(0);
v___x_224_ = l_Lean_Meta_Sym_mkPatternFromExpr(v_a_221_, v___x_222_, v___x_223_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
return v___x_224_;
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec_ref(v_paramNames_212_);
v_a_225_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_220_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_220_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v_paramNames_212_);
v_a_233_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_215_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_215_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
v_a_241_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_210_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_210_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkSimprocPatternFromExpr___boxed(lean_object* v_e_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Elab_mkSimprocPatternFromExpr(v_e_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocKeys(lean_object* v_stx_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Elab_elabCbvSimprocPattern(v_stx_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
v___x_264_ = l_Lean_Elab_mkSimprocPatternFromExpr(v_a_263_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_273_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_273_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_a_265_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_269_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_264_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_264_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_a_282_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_262_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_262_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabCbvSimprocKeys___boxed(lean_object* v_stx_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Elab_elabCbvSimprocKeys(v_stx_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
return v_res_296_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_297_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_300_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_301_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
lean_ctor_set(v___x_303_, 2, v___x_302_);
lean_ctor_set(v___x_303_, 3, v___x_302_);
lean_ctor_set(v___x_303_, 4, v___x_301_);
lean_ctor_set(v___x_303_, 5, v___x_301_);
lean_ctor_set(v___x_303_, 6, v___x_301_);
lean_ctor_set(v___x_303_, 7, v___x_301_);
lean_ctor_set(v___x_303_, 8, v___x_301_);
lean_ctor_set(v___x_303_, 9, v___x_301_);
lean_ctor_set(v___x_303_, 10, v___x_301_);
lean_ctor_set(v___x_303_, 11, v___x_300_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_unsigned_to_nat(32u);
v___x_305_ = lean_mk_empty_array_with_capacity(v___x_304_);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_307_ = ((size_t)5ULL);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_unsigned_to_nat(32u);
v___x_310_ = lean_mk_empty_array_with_capacity(v___x_309_);
v___x_311_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3);
v___x_312_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v___x_310_);
lean_ctor_set(v___x_312_, 2, v___x_308_);
lean_ctor_set(v___x_312_, 3, v___x_308_);
lean_ctor_set_usize(v___x_312_, 4, v___x_307_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_box(1);
v___x_314_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4);
v___x_315_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1);
v___x_316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(lean_object* v_msgData_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; lean_object* v_toCold_322_; lean_object* v_env_323_; lean_object* v_options_324_; uint8_t v___x_325_; lean_object* v_env_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_321_ = lean_st_ref_get(v___y_319_);
v_toCold_322_ = lean_ctor_get(v___y_318_, 0);
v_env_323_ = lean_ctor_get(v___x_321_, 0);
lean_inc_ref(v_env_323_);
lean_dec(v___x_321_);
v_options_324_ = lean_ctor_get(v_toCold_322_, 2);
v___x_325_ = 0;
v_env_326_ = l_Lean_Environment_setRecordingDeps(v_env_323_, v___x_325_);
v___x_327_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2);
v___x_328_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_324_);
v___x_329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_329_, 0, v_env_326_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
lean_ctor_set(v___x_329_, 2, v___x_328_);
lean_ctor_set(v___x_329_, 3, v_options_324_);
v___x_330_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v_msgData_317_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___boxed(lean_object* v_msgData_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(v_msgData_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_ref_341_; lean_object* v___x_342_; lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_351_; 
v_ref_341_ = lean_ctor_get(v___y_338_, 2);
v___x_342_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(v_msg_337_, v___y_338_, v___y_339_);
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_351_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_349_; 
lean_inc(v_ref_341_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_ref_341_);
lean_ctor_set(v___x_347_, 1, v_a_343_);
if (v_isShared_346_ == 0)
{
lean_ctor_set_tag(v___x_345_, 1);
lean_ctor_set(v___x_345_, 0, v___x_347_);
v___x_349_ = v___x_345_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg___boxed(lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(v_msg_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_378_, lean_object* v_declHint_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_env_384_; uint8_t v___x_385_; 
v___x_382_ = lean_box(0);
v___x_383_ = lean_st_ref_get(v___y_380_);
v_env_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_env_384_);
lean_dec(v___x_383_);
v___x_385_ = l_Lean_Name_isAnonymous(v_declHint_379_);
if (v___x_385_ == 0)
{
uint8_t v_isExporting_386_; 
v_isExporting_386_ = lean_ctor_get_uint8(v_env_384_, sizeof(void*)*13);
if (v_isExporting_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec_ref(v_env_384_);
lean_dec(v_declHint_379_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v_msg_378_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; uint8_t v___x_389_; 
lean_inc_ref(v_env_384_);
v___x_388_ = l_Lean_Environment_setExporting(v_env_384_, v___x_385_);
lean_inc(v_declHint_379_);
lean_inc_ref(v___x_388_);
v___x_389_ = l_Lean_Environment_contains(v___x_388_, v_declHint_379_, v_isExporting_386_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
lean_dec_ref(v___x_388_);
lean_dec_ref(v_env_384_);
lean_dec(v_declHint_379_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v_msg_378_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_c_396_; lean_object* v___x_397_; 
v___x_391_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2);
v___x_392_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5);
v___x_393_ = l_Lean_Options_empty;
v___x_394_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_394_, 0, v___x_388_);
lean_ctor_set(v___x_394_, 1, v___x_391_);
lean_ctor_set(v___x_394_, 2, v___x_392_);
lean_ctor_set(v___x_394_, 3, v___x_393_);
lean_inc(v_declHint_379_);
v___x_395_ = l_Lean_MessageData_ofConstName(v_declHint_379_, v___x_385_);
v_c_396_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_396_, 0, v___x_394_);
lean_ctor_set(v_c_396_, 1, v___x_395_);
v___x_397_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_384_, v_declHint_379_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref(v_env_384_);
lean_dec(v_declHint_379_);
v___x_398_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v_c_396_);
v___x_400_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = l_Lean_MessageData_note(v___x_401_);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v_msg_378_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_439_; 
v_val_405_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_439_ == 0)
{
v___x_407_ = v___x_397_;
v_isShared_408_ = v_isSharedCheck_439_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_val_405_);
lean_dec(v___x_397_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_439_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v_mod_411_; uint8_t v___x_412_; 
v___x_409_ = l_Lean_Environment_header(v_env_384_);
lean_dec_ref(v_env_384_);
v___x_410_ = l_Lean_EnvironmentHeader_moduleNames(v___x_409_);
v_mod_411_ = lean_array_get(v___x_382_, v___x_410_, v_val_405_);
lean_dec(v_val_405_);
lean_dec_ref(v___x_410_);
v___x_412_ = l_Lean_isPrivateName(v_declHint_379_);
lean_dec(v_declHint_379_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_413_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v_c_396_);
v___x_415_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = l_Lean_MessageData_ofName(v_mod_411_);
v___x_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = l_Lean_MessageData_note(v___x_420_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v_msg_378_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
lean_ctor_set(v___x_407_, 0, v___x_422_);
v___x_424_ = v___x_407_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_426_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v_c_396_);
v___x_428_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = l_Lean_MessageData_ofName(v_mod_411_);
v___x_431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = l_Lean_MessageData_note(v___x_433_);
v___x_435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_435_, 0, v_msg_378_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
lean_ctor_set(v___x_407_, 0, v___x_435_);
v___x_437_ = v___x_407_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
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
}
}
}
else
{
lean_object* v___x_440_; 
lean_dec_ref(v_env_384_);
lean_dec(v_declHint_379_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_msg_378_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_441_, lean_object* v_declHint_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_441_, v_declHint_442_, v___y_443_);
lean_dec(v___y_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_446_, lean_object* v_declHint_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_461_; 
v___x_451_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_446_, v_declHint_447_, v___y_449_);
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_461_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_456_ = l_Lean_unknownIdentifierMessageTag;
v___x_457_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v_a_452_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_457_);
v___x_459_ = v___x_454_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_462_, lean_object* v_declHint_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_462_, v_declHint_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_468_, lean_object* v_msg_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_toCold_473_; lean_object* v_currRecDepth_474_; lean_object* v_ref_475_; uint16_t v_optionFlags_476_; uint8_t v_suppressElabErrors_477_; uint8_t v_isRecordingDeps_478_; lean_object* v_ref_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_toCold_473_ = lean_ctor_get(v___y_470_, 0);
v_currRecDepth_474_ = lean_ctor_get(v___y_470_, 1);
v_ref_475_ = lean_ctor_get(v___y_470_, 2);
v_optionFlags_476_ = lean_ctor_get_uint16(v___y_470_, sizeof(void*)*3);
v_suppressElabErrors_477_ = lean_ctor_get_uint8(v___y_470_, sizeof(void*)*3 + 2);
v_isRecordingDeps_478_ = lean_ctor_get_uint8(v___y_470_, sizeof(void*)*3 + 3);
v_ref_479_ = l_Lean_replaceRef(v_ref_468_, v_ref_475_);
lean_inc(v_currRecDepth_474_);
lean_inc_ref(v_toCold_473_);
v___x_480_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_480_, 0, v_toCold_473_);
lean_ctor_set(v___x_480_, 1, v_currRecDepth_474_);
lean_ctor_set(v___x_480_, 2, v_ref_479_);
lean_ctor_set_uint16(v___x_480_, sizeof(void*)*3, v_optionFlags_476_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*3 + 2, v_suppressElabErrors_477_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*3 + 3, v_isRecordingDeps_478_);
v___x_481_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(v_msg_469_, v___x_480_, v___y_471_);
lean_dec_ref_known(v___x_480_, 3);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_482_, lean_object* v_msg_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_482_, v_msg_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v_ref_482_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_488_, lean_object* v_msg_489_, lean_object* v_declHint_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; lean_object* v_a_495_; lean_object* v___x_496_; 
v___x_494_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_489_, v_declHint_490_, v___y_491_, v___y_492_);
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref(v___x_494_);
v___x_496_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_488_, v_a_495_, v___y_491_, v___y_492_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_497_, lean_object* v_msg_498_, lean_object* v_declHint_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_497_, v_msg_498_, v_declHint_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v_ref_497_);
return v_res_503_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_509_ = l_Lean_stringToMessageData(v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_510_, lean_object* v_constName_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_515_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_516_ = 0;
lean_inc(v_constName_511_);
v___x_517_ = l_Lean_MessageData_ofConstName(v_constName_511_, v___x_516_);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_515_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_510_, v___x_520_, v_constName_511_, v___y_512_, v___y_513_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_522_, lean_object* v_constName_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_522_, v_constName_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v_ref_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(lean_object* v_constName_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_ref_532_; lean_object* v___x_533_; 
v_ref_532_ = lean_ctor_get(v___y_529_, 2);
v___x_533_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_532_, v_constName_528_, v___y_529_, v___y_530_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(lean_object* v_constName_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___x_543_; lean_object* v_env_544_; uint8_t v___x_545_; lean_object* v___x_546_; 
v___x_543_ = lean_st_ref_get(v___y_541_);
v_env_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc_ref(v_env_544_);
lean_dec(v___x_543_);
v___x_545_ = 0;
lean_inc(v_constName_539_);
v___x_546_ = l_Lean_Environment_find_x3f(v_env_544_, v_constName_539_, v___x_545_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_539_, v___y_540_, v___y_541_);
return v___x_547_;
}
else
{
lean_object* v_val_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v_constName_539_);
v_val_548_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_546_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_val_548_);
lean_dec(v___x_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set_tag(v___x_550_, 0);
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_val_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0___boxed(lean_object* v_constName_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(v_constName_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_560_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__1(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__0));
v___x_563_ = l_Lean_stringToMessageData(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__8(void){
_start:
{
uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = 0;
v___x_576_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__7));
v___x_577_ = l_Lean_MessageData_ofConstName(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__9(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__8, &l_Lean_Elab_checkCbvSimprocType___closed__8_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__8);
v___x_579_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__1, &l_Lean_Elab_checkCbvSimprocType___closed__1_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__1);
v___x_580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__11(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__10));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__12(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__11, &l_Lean_Elab_checkCbvSimprocType___closed__11_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__11);
v___x_585_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__9, &l_Lean_Elab_checkCbvSimprocType___closed__9_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__9);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__14(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__13));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkCbvSimprocType(lean_object* v_declName_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_594_; 
lean_inc(v_declName_590_);
v___x_594_ = l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(v_declName_590_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_637_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_637_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_637_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_637_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___x_611_; 
v___x_611_ = l_Lean_ConstantInfo_type(v_a_595_);
if (lean_obj_tag(v___x_611_) == 4)
{
lean_object* v_declName_612_; 
v_declName_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_declName_612_);
lean_dec_ref_known(v___x_611_, 2);
if (lean_obj_tag(v_declName_612_) == 1)
{
lean_object* v_pre_613_; 
v_pre_613_ = lean_ctor_get(v_declName_612_, 0);
lean_inc(v_pre_613_);
if (lean_obj_tag(v_pre_613_) == 1)
{
lean_object* v_pre_614_; 
v_pre_614_ = lean_ctor_get(v_pre_613_, 0);
lean_inc(v_pre_614_);
if (lean_obj_tag(v_pre_614_) == 1)
{
lean_object* v_pre_615_; 
v_pre_615_ = lean_ctor_get(v_pre_614_, 0);
lean_inc(v_pre_615_);
if (lean_obj_tag(v_pre_615_) == 1)
{
lean_object* v_pre_616_; 
v_pre_616_ = lean_ctor_get(v_pre_615_, 0);
lean_inc(v_pre_616_);
if (lean_obj_tag(v_pre_616_) == 1)
{
lean_object* v_pre_617_; 
v_pre_617_ = lean_ctor_get(v_pre_616_, 0);
if (lean_obj_tag(v_pre_617_) == 0)
{
lean_object* v_str_618_; lean_object* v_str_619_; lean_object* v_str_620_; lean_object* v_str_621_; lean_object* v_str_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_str_618_ = lean_ctor_get(v_declName_612_, 1);
lean_inc_ref(v_str_618_);
lean_dec_ref_known(v_declName_612_, 2);
v_str_619_ = lean_ctor_get(v_pre_613_, 1);
lean_inc_ref(v_str_619_);
lean_dec_ref_known(v_pre_613_, 2);
v_str_620_ = lean_ctor_get(v_pre_614_, 1);
lean_inc_ref(v_str_620_);
lean_dec_ref_known(v_pre_614_, 2);
v_str_621_ = lean_ctor_get(v_pre_615_, 1);
lean_inc_ref(v_str_621_);
lean_dec_ref_known(v_pre_615_, 2);
v_str_622_ = lean_ctor_get(v_pre_616_, 1);
lean_inc_ref(v_str_622_);
lean_dec_ref_known(v_pre_616_, 2);
v___x_623_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__2));
v___x_624_ = lean_string_dec_eq(v_str_622_, v___x_623_);
lean_dec_ref(v_str_622_);
if (v___x_624_ == 0)
{
lean_dec_ref(v_str_621_);
lean_dec_ref(v_str_620_);
lean_dec_ref(v_str_619_);
lean_dec_ref(v_str_618_);
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
else
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__3));
v___x_626_ = lean_string_dec_eq(v_str_621_, v___x_625_);
lean_dec_ref(v_str_621_);
if (v___x_626_ == 0)
{
lean_dec_ref(v_str_620_);
lean_dec_ref(v_str_619_);
lean_dec_ref(v_str_618_);
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
else
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__4));
v___x_628_ = lean_string_dec_eq(v_str_620_, v___x_627_);
lean_dec_ref(v_str_620_);
if (v___x_628_ == 0)
{
lean_dec_ref(v_str_619_);
lean_dec_ref(v_str_618_);
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
else
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__5));
v___x_630_ = lean_string_dec_eq(v_str_619_, v___x_629_);
lean_dec_ref(v_str_619_);
if (v___x_630_ == 0)
{
lean_dec_ref(v_str_618_);
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
else
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__6));
v___x_632_ = lean_string_dec_eq(v_str_618_, v___x_631_);
lean_dec_ref(v_str_618_);
if (v___x_632_ == 0)
{
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
else
{
lean_object* v___x_633_; lean_object* v___x_635_; 
lean_dec(v_a_595_);
lean_dec(v_declName_590_);
v___x_633_ = lean_box(0);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_633_);
v___x_635_ = v___x_597_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_616_, 2);
lean_dec_ref_known(v_pre_615_, 2);
lean_dec_ref_known(v_pre_614_, 2);
lean_dec_ref_known(v_pre_613_, 2);
lean_dec_ref_known(v_declName_612_, 2);
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
}
else
{
lean_dec_ref_known(v_pre_615_, 2);
lean_dec(v_pre_616_);
lean_dec_ref_known(v_pre_614_, 2);
lean_dec_ref_known(v_pre_613_, 2);
lean_dec_ref_known(v_declName_612_, 2);
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
}
else
{
lean_dec(v_pre_615_);
lean_dec_ref_known(v_pre_614_, 2);
lean_dec_ref_known(v_pre_613_, 2);
lean_dec_ref_known(v_declName_612_, 2);
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
}
else
{
lean_dec(v_pre_614_);
lean_dec_ref_known(v_pre_613_, 2);
lean_dec_ref_known(v_declName_612_, 2);
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
}
else
{
lean_dec_ref_known(v_declName_612_, 2);
lean_dec(v_pre_613_);
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
}
else
{
lean_dec(v_declName_612_);
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
}
else
{
lean_dec_ref(v___x_611_);
lean_del_object(v___x_597_);
v___y_600_ = v_a_591_;
v___y_601_ = v_a_592_;
goto v___jp_599_;
}
v___jp_599_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_602_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__12, &l_Lean_Elab_checkCbvSimprocType___closed__12_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__12);
v___x_603_ = l_Lean_MessageData_ofName(v_declName_590_);
v___x_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__14, &l_Lean_Elab_checkCbvSimprocType___closed__14_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__14);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_Lean_ConstantInfo_type(v_a_595_);
lean_dec(v_a_595_);
v___x_608_ = l_Lean_indentExpr(v___x_607_);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_606_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(v___x_609_, v___y_600_, v___y_601_);
return v___x_610_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_declName_590_);
v_a_638_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_594_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_594_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkCbvSimprocType___boxed(lean_object* v_declName_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Elab_checkCbvSimprocType(v_declName_646_, v_a_647_, v_a_648_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1(lean_object* v_00_u03b1_651_, lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(v_msg_652_, v___y_653_, v___y_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___boxed(lean_object* v_00_u03b1_657_, lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1(v_00_u03b1_657_, v_msg_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0(lean_object* v_00_u03b1_663_, lean_object* v_constName_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_664_, v___y_665_, v___y_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_669_, lean_object* v_constName_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0(v_00_u03b1_669_, v_constName_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_675_, lean_object* v_ref_676_, lean_object* v_constName_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_676_, v_constName_677_, v___y_678_, v___y_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_682_, lean_object* v_ref_683_, lean_object* v_constName_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1(v_00_u03b1_682_, v_ref_683_, v_constName_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v_ref_683_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_689_, lean_object* v_ref_690_, lean_object* v_msg_691_, lean_object* v_declHint_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_690_, v_msg_691_, v_declHint_692_, v___y_693_, v___y_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_697_, lean_object* v_ref_698_, lean_object* v_msg_699_, lean_object* v_declHint_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_697_, v_ref_698_, v_msg_699_, v_declHint_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v_ref_698_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_705_, lean_object* v_declHint_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_705_, v_declHint_706_, v___y_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_711_, lean_object* v_declHint_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_711_, v_declHint_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_717_, lean_object* v_ref_718_, lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_718_, v_msg_719_, v___y_720_, v___y_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_724_, lean_object* v_ref_725_, lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_724_, v_ref_725_, v_msg_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v_ref_725_);
return v_res_730_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_box(0);
v___x_732_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg(){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0);
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___boxed(lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0(lean_object* v_00_u03b1_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___boxed(lean_object* v_00_u03b1_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0(v_00_u03b1_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0(lean_object* v___x_749_, lean_object* v___x_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_realizeGlobalConstNoOverload(v___x_749_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc_n(v_a_759_, 2);
lean_dec_ref_known(v___x_758_, 1);
v___x_760_ = l_Lean_Elab_checkCbvSimprocType(v_a_759_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v___x_761_; 
lean_dec_ref_known(v___x_760_, 1);
v___x_761_ = l_Lean_Elab_elabCbvSimprocKeys(v___x_750_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(v_a_759_, v_a_762_, v___y_755_, v___y_756_);
return v___x_763_;
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_a_759_);
v_a_764_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_761_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_761_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_dec(v_a_759_);
lean_dec(v___x_750_);
return v___x_760_;
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec(v___x_750_);
v_a_772_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_758_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_758_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0___boxed(lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0(v___x_780_, v___x_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern(lean_object* v_stx_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2));
lean_inc(v_stx_796_);
v___x_801_ = l_Lean_Syntax_isOfKind(v_stx_796_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
lean_dec(v_stx_796_);
v___x_802_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
return v___x_802_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___x_808_; 
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = l_Lean_Syntax_getArg(v_stx_796_, v___x_803_);
v___x_805_ = lean_unsigned_to_nat(3u);
v___x_806_ = l_Lean_Syntax_getArg(v_stx_796_, v___x_805_);
lean_dec(v_stx_796_);
v___f_807_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0___boxed), 9, 2);
lean_closure_set(v___f_807_, 0, v___x_806_);
lean_closure_set(v___f_807_, 1, v___x_804_);
v___x_808_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_807_, v_a_797_, v_a_798_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___boxed(lean_object* v_stx_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Elab_Command_elabCbvSimprocPattern(v_stx_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1(){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_823_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_824_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2));
v___x_825_ = ((lean_object*)(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3));
v___x_826_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCbvSimprocPattern___boxed), 4, 0);
v___x_827_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_823_, v___x_824_, v___x_825_, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___boxed(lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1();
return v_res_829_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_box(0);
v___x_840_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3));
v___x_841_ = l_Lean_mkConst(v___x_840_, v___x_839_);
return v___x_841_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_box(0);
v___x_850_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6));
v___x_851_ = l_Lean_mkConst(v___x_850_, v___x_849_);
return v___x_851_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_box(0);
v___x_860_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9));
v___x_861_ = l_Lean_mkConst(v___x_860_, v___x_859_);
return v___x_861_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = lean_box(0);
v___x_869_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13));
v___x_870_ = l_Lean_mkConst(v___x_869_, v___x_868_);
return v___x_870_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = lean_box(0);
v___x_877_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16));
v___x_878_ = l_Lean_mkConst(v___x_877_, v___x_876_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = lean_box(0);
v___x_887_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19));
v___x_888_ = l_Lean_mkConst(v___x_887_, v___x_886_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
v___x_896_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23));
v___x_897_ = l_Lean_mkConst(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_box(0);
v___x_906_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26));
v___x_907_ = l_Lean_mkConst(v___x_906_, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = lean_box(0);
v___x_916_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29));
v___x_917_ = l_Lean_mkConst(v___x_916_, v___x_915_);
return v___x_917_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_box(0);
v___x_926_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32));
v___x_927_ = l_Lean_mkConst(v___x_926_, v___x_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(lean_object* v_nilFn_928_, lean_object* v_consFn_929_, lean_object* v_x_930_){
_start:
{
if (lean_obj_tag(v_x_930_) == 0)
{
lean_dec_ref(v_consFn_929_);
lean_inc_ref(v_nilFn_928_);
return v_nilFn_928_;
}
else
{
lean_object* v_head_931_; lean_object* v_tail_932_; lean_object* v___y_934_; 
v_head_931_ = lean_ctor_get(v_x_930_, 0);
lean_inc(v_head_931_);
v_tail_932_ = lean_ctor_get(v_x_930_, 1);
lean_inc(v_tail_932_);
lean_dec_ref_known(v_x_930_, 2);
switch(lean_obj_tag(v_head_931_))
{
case 0:
{
lean_object* v___x_937_; 
v___x_937_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4);
v___y_934_ = v___x_937_;
goto v___jp_933_;
}
case 1:
{
lean_object* v___x_938_; 
v___x_938_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7);
v___y_934_ = v___x_938_;
goto v___jp_933_;
}
case 2:
{
lean_object* v_a_939_; lean_object* v___x_940_; 
v_a_939_ = lean_ctor_get(v_head_931_, 0);
lean_inc_ref(v_a_939_);
lean_dec_ref_known(v_head_931_, 1);
v___x_940_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10);
if (lean_obj_tag(v_a_939_) == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_941_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14);
v___x_942_ = l_Lean_Expr_lit___override(v_a_939_);
v___x_943_ = l_Lean_Expr_app___override(v___x_941_, v___x_942_);
v___x_944_ = l_Lean_Expr_app___override(v___x_940_, v___x_943_);
v___y_934_ = v___x_944_;
goto v___jp_933_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_945_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17);
v___x_946_ = l_Lean_Expr_lit___override(v_a_939_);
v___x_947_ = l_Lean_Expr_app___override(v___x_945_, v___x_946_);
v___x_948_ = l_Lean_Expr_app___override(v___x_940_, v___x_947_);
v___y_934_ = v___x_948_;
goto v___jp_933_;
}
}
case 3:
{
lean_object* v_a_949_; lean_object* v_a_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_a_949_ = lean_ctor_get(v_head_931_, 0);
lean_inc(v_a_949_);
v_a_950_ = lean_ctor_get(v_head_931_, 1);
lean_inc(v_a_950_);
lean_dec_ref_known(v_head_931_, 2);
v___x_951_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20);
v___x_952_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24);
v___x_953_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_949_);
v___x_954_ = l_Lean_Expr_app___override(v___x_952_, v___x_953_);
v___x_955_ = l_Lean_mkNatLit(v_a_950_);
v___x_956_ = l_Lean_mkAppB(v___x_951_, v___x_954_, v___x_955_);
v___y_934_ = v___x_956_;
goto v___jp_933_;
}
case 4:
{
lean_object* v_a_957_; lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_a_957_ = lean_ctor_get(v_head_931_, 0);
lean_inc(v_a_957_);
v_a_958_ = lean_ctor_get(v_head_931_, 1);
lean_inc(v_a_958_);
lean_dec_ref_known(v_head_931_, 2);
v___x_959_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27);
v___x_960_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_957_);
v___x_961_ = l_Lean_mkNatLit(v_a_958_);
v___x_962_ = l_Lean_mkAppB(v___x_959_, v___x_960_, v___x_961_);
v___y_934_ = v___x_962_;
goto v___jp_933_;
}
case 5:
{
lean_object* v___x_963_; 
v___x_963_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30);
v___y_934_ = v___x_963_;
goto v___jp_933_;
}
default: 
{
lean_object* v_a_964_; lean_object* v_a_965_; lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_a_964_ = lean_ctor_get(v_head_931_, 0);
lean_inc(v_a_964_);
v_a_965_ = lean_ctor_get(v_head_931_, 1);
lean_inc(v_a_965_);
v_a_966_ = lean_ctor_get(v_head_931_, 2);
lean_inc(v_a_966_);
lean_dec_ref_known(v_head_931_, 3);
v___x_967_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33);
v___x_968_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_964_);
v___x_969_ = l_Lean_mkNatLit(v_a_965_);
v___x_970_ = l_Lean_mkNatLit(v_a_966_);
v___x_971_ = l_Lean_mkApp3(v___x_967_, v___x_968_, v___x_969_, v___x_970_);
v___y_934_ = v___x_971_;
goto v___jp_933_;
}
}
v___jp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_inc_ref(v_consFn_929_);
v___x_935_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nilFn_928_, v_consFn_929_, v_tail_932_);
v___x_936_ = l_Lean_mkAppB(v_consFn_929_, v___y_934_, v___x_935_);
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___boxed(lean_object* v_nilFn_972_, lean_object* v_consFn_973_, lean_object* v_x_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nilFn_972_, v_consFn_973_, v_x_974_);
lean_dec_ref(v_nilFn_972_);
return v_res_975_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6));
v___x_988_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5));
v___x_989_ = l_Lean_mkConst(v___x_988_, v___x_987_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6));
v___x_995_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9));
v___x_996_ = l_Lean_mkConst(v___x_995_, v___x_994_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6));
v___x_1002_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12));
v___x_1003_ = l_Lean_mkConst(v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0(lean_object* v___x_1007_, lean_object* v___x_1008_, lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_realizeGlobalConstNoOverload(v___x_1007_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc_n(v_a_1019_, 2);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = l_Lean_Elab_checkCbvSimprocType(v_a_1019_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref_known(v___x_1020_, 1);
v___x_1021_ = l_Lean_Elab_elabCbvSimprocKeys(v___x_1008_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_nil_1037_; lean_object* v___x_1038_; lean_object* v_cons_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__3));
v___x_1024_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0));
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1));
v___x_1026_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2));
lean_inc_ref(v___x_1009_);
v___x_1027_ = l_Lean_Name_mkStr5(v___x_1009_, v___x_1023_, v___x_1024_, v___x_1025_, v___x_1026_);
v___x_1028_ = lean_box(0);
v___x_1029_ = l_Lean_mkConst(v___x_1027_, v___x_1028_);
lean_inc_n(v_a_1019_, 2);
v___x_1030_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_1019_);
v___x_1031_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0));
v___x_1032_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1));
v___x_1033_ = l_Lean_Name_mkStr4(v___x_1009_, v___x_1023_, v___x_1031_, v___x_1032_);
v___x_1034_ = l_Lean_mkConst(v___x_1033_, v___x_1028_);
v___x_1035_ = lean_obj_once(&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7, &l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7_once, _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7);
v___x_1036_ = lean_obj_once(&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10, &l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_once, _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10);
lean_inc_ref_n(v___x_1034_, 2);
v_nil_1037_ = l_Lean_Expr_app___override(v___x_1036_, v___x_1034_);
v___x_1038_ = lean_obj_once(&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13, &l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_once, _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13);
v_cons_1039_ = l_Lean_Expr_app___override(v___x_1038_, v___x_1034_);
v___x_1040_ = lean_array_to_list(v_a_1022_);
v___x_1041_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nil_1037_, v_cons_1039_, v___x_1040_);
lean_dec_ref(v_nil_1037_);
v___x_1042_ = l_Lean_mkAppB(v___x_1035_, v___x_1034_, v___x_1041_);
v___x_1043_ = l_Lean_mkConst(v_a_1019_, v___x_1028_);
v___x_1044_ = lean_mk_empty_array_with_capacity(v___x_1010_);
v___x_1045_ = lean_array_push(v___x_1044_, v___x_1030_);
v___x_1046_ = lean_array_push(v___x_1045_, v___x_1042_);
v___x_1047_ = lean_array_push(v___x_1046_, v___x_1043_);
v___x_1048_ = l_Lean_mkAppN(v___x_1029_, v___x_1047_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15));
v___x_1050_ = l_Lean_Name_append(v_a_1019_, v___x_1049_);
v___x_1051_ = l_Lean_Core_mkFreshUserName(v___x_1050_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = l_Lean_declareBuiltin(v_a_1052_, v___x_1048_, v___y_1015_, v___y_1016_);
return v___x_1053_;
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v___x_1048_);
v_a_1054_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1051_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1051_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_a_1019_);
lean_dec_ref(v___x_1009_);
v_a_1062_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1021_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1021_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_dec(v_a_1019_);
lean_dec_ref(v___x_1009_);
lean_dec(v___x_1008_);
return v___x_1020_;
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref(v___x_1009_);
lean_dec(v___x_1008_);
v_a_1070_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1018_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1018_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___boxed(lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v___x_1080_, lean_object* v___x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0(v___x_1078_, v___x_1079_, v___x_1080_, v___x_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___x_1081_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin(lean_object* v_stx_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__2));
v___x_1100_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1));
lean_inc(v_stx_1095_);
v___x_1101_ = l_Lean_Syntax_isOfKind(v_stx_1095_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_dec(v_stx_1095_);
v___x_1102_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
return v___x_1102_;
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; 
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = l_Lean_Syntax_getArg(v_stx_1095_, v___x_1103_);
v___x_1105_ = lean_unsigned_to_nat(3u);
v___x_1106_ = l_Lean_Syntax_getArg(v_stx_1095_, v___x_1105_);
lean_dec(v_stx_1095_);
v___f_1107_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1107_, 0, v___x_1106_);
lean_closure_set(v___f_1107_, 1, v___x_1104_);
lean_closure_set(v___f_1107_, 2, v___x_1099_);
lean_closure_set(v___f_1107_, 3, v___x_1105_);
v___x_1108_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1107_, v_a_1096_, v_a_1097_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___boxed(lean_object* v_stx_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin(v_stx_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1(){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1121_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1122_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1));
v___x_1123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1));
v___x_1124_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___boxed), 4, 0);
v___x_1125_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1121_, v___x_1122_, v___x_1123_, v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___boxed(lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1();
return v_res_1127_;
}
}
lean_object* runtime_initialize_Init_CbvSimproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_CbvSimproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
}
#ifdef __cplusplus
}
#endif
