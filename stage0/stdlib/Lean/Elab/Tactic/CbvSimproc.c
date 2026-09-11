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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_Sym_mkPatternFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declare"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(12, 217, 76, 92, 115, 157, 174, 191)}};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value;
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12;
static const lean_string_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15;
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
uint8_t v___x_356__boxed_47_; lean_object* v_res_48_; 
v___x_356__boxed_47_ = lean_unbox(v___x_39_);
v_res_48_ = l_Lean_Elab_elabCbvSimprocPattern___lam__1(v_stx_37_, v___x_38_, v___x_356__boxed_47_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
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
uint8_t v___x_208_; lean_object* v___x_209_; 
v___x_208_ = 1;
v___x_209_ = l_Lean_Meta_abstractMVars(v_e_202_, v___x_208_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v_paramNames_211_; lean_object* v_expr_212_; lean_object* v___f_213_; uint8_t v___x_214_; lean_object* v___x_215_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
v_paramNames_211_ = lean_ctor_get(v_a_210_, 0);
lean_inc_ref(v_paramNames_211_);
v_expr_212_ = lean_ctor_get(v_a_210_, 2);
lean_inc_ref(v_expr_212_);
lean_dec(v_a_210_);
v___f_213_ = ((lean_object*)(l_Lean_Elab_mkSimprocPatternFromExpr___closed__0));
v___x_214_ = 0;
v___x_215_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(v_expr_212_, v___f_213_, v___x_214_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
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
v___x_222_ = lean_array_to_list(v_paramNames_211_);
v___x_223_ = lean_box(0);
v___x_224_ = l_Lean_Meta_Sym_mkPatternFromExpr(v_a_221_, v___x_222_, v___x_223_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
return v___x_224_;
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec_ref(v_paramNames_211_);
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
lean_dec_ref(v_paramNames_211_);
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
v_a_241_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_209_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_209_);
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
v___x_297_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1);
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
lean_ctor_set(v___x_302_, 2, v___x_301_);
lean_ctor_set(v___x_302_, 3, v___x_301_);
lean_ctor_set(v___x_302_, 4, v___x_300_);
lean_ctor_set(v___x_302_, 5, v___x_300_);
lean_ctor_set(v___x_302_, 6, v___x_300_);
lean_ctor_set(v___x_302_, 7, v___x_300_);
lean_ctor_set(v___x_302_, 8, v___x_300_);
lean_ctor_set(v___x_302_, 9, v___x_300_);
lean_ctor_set(v___x_302_, 10, v___x_300_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_unsigned_to_nat(32u);
v___x_304_ = lean_mk_empty_array_with_capacity(v___x_303_);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_306_ = ((size_t)5ULL);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_unsigned_to_nat(32u);
v___x_309_ = lean_mk_empty_array_with_capacity(v___x_308_);
v___x_310_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3);
v___x_311_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_309_);
lean_ctor_set(v___x_311_, 2, v___x_307_);
lean_ctor_set(v___x_311_, 3, v___x_307_);
lean_ctor_set_usize(v___x_311_, 4, v___x_306_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = lean_box(1);
v___x_313_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4);
v___x_314_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1);
v___x_315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
lean_ctor_set(v___x_315_, 2, v___x_312_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(lean_object* v_msgData_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; lean_object* v_toCold_321_; lean_object* v_env_322_; lean_object* v_options_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_320_ = lean_st_ref_get(v___y_318_);
v_toCold_321_ = lean_ctor_get(v___y_317_, 0);
v_env_322_ = lean_ctor_get(v___x_320_, 0);
lean_inc_ref(v_env_322_);
lean_dec(v___x_320_);
v_options_323_ = lean_ctor_get(v_toCold_321_, 2);
v___x_324_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2);
v___x_325_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_323_);
v___x_326_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_326_, 0, v_env_322_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
lean_ctor_set(v___x_326_, 2, v___x_325_);
lean_ctor_set(v___x_326_, 3, v_options_323_);
v___x_327_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v_msgData_316_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___boxed(lean_object* v_msgData_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(v_msgData_329_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(lean_object* v_msg_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_ref_338_; lean_object* v___x_339_; lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_ref_338_ = lean_ctor_get(v___y_335_, 2);
v___x_339_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(v_msg_334_, v___y_335_, v___y_336_);
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
lean_inc(v_ref_338_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_ref_338_);
lean_ctor_set(v___x_344_, 1, v_a_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set_tag(v___x_342_, 1);
lean_ctor_set(v___x_342_, 0, v___x_344_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg___boxed(lean_object* v_msg_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(v_msg_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_353_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_356_ = l_Lean_stringToMessageData(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_375_, lean_object* v_declHint_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; lean_object* v_env_380_; uint8_t v___x_381_; 
v___x_379_ = lean_st_ref_get(v___y_377_);
v_env_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc_ref(v_env_380_);
lean_dec(v___x_379_);
v___x_381_ = l_Lean_Name_isAnonymous(v_declHint_376_);
if (v___x_381_ == 0)
{
uint8_t v_isExporting_382_; 
v_isExporting_382_ = lean_ctor_get_uint8(v_env_380_, sizeof(void*)*8);
if (v_isExporting_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec_ref(v_env_380_);
lean_dec(v_declHint_376_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v_msg_375_);
return v___x_383_;
}
else
{
lean_object* v___x_384_; uint8_t v___x_385_; 
lean_inc_ref(v_env_380_);
v___x_384_ = l_Lean_Environment_setExporting(v_env_380_, v___x_381_);
lean_inc(v_declHint_376_);
lean_inc_ref(v___x_384_);
v___x_385_ = l_Lean_Environment_contains(v___x_384_, v_declHint_376_, v_isExporting_382_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec_ref(v___x_384_);
lean_dec_ref(v_env_380_);
lean_dec(v_declHint_376_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v_msg_375_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_c_392_; lean_object* v___x_393_; 
v___x_387_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2);
v___x_388_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5);
v___x_389_ = l_Lean_Options_empty;
v___x_390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_390_, 0, v___x_384_);
lean_ctor_set(v___x_390_, 1, v___x_387_);
lean_ctor_set(v___x_390_, 2, v___x_388_);
lean_ctor_set(v___x_390_, 3, v___x_389_);
lean_inc(v_declHint_376_);
v___x_391_ = l_Lean_MessageData_ofConstName(v_declHint_376_, v___x_381_);
v_c_392_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_392_, 0, v___x_390_);
lean_ctor_set(v_c_392_, 1, v___x_391_);
v___x_393_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_380_, v_declHint_376_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec_ref(v_env_380_);
lean_dec(v_declHint_376_);
v___x_394_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v_c_392_);
v___x_396_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_MessageData_note(v___x_397_);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v_msg_375_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
else
{
lean_object* v_val_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_436_; 
v_val_401_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_436_ == 0)
{
v___x_403_ = v___x_393_;
v_isShared_404_ = v_isSharedCheck_436_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_val_401_);
lean_dec(v___x_393_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_436_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_mod_408_; uint8_t v___x_409_; 
v___x_405_ = lean_box(0);
v___x_406_ = l_Lean_Environment_header(v_env_380_);
lean_dec_ref(v_env_380_);
v___x_407_ = l_Lean_EnvironmentHeader_moduleNames(v___x_406_);
v_mod_408_ = lean_array_get(v___x_405_, v___x_407_, v_val_401_);
lean_dec(v_val_401_);
lean_dec_ref(v___x_407_);
v___x_409_ = l_Lean_isPrivateName(v_declHint_376_);
lean_dec(v_declHint_376_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_410_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_c_392_);
v___x_412_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = l_Lean_MessageData_ofName(v_mod_408_);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_MessageData_note(v___x_417_);
v___x_419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_419_, 0, v_msg_375_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 0);
lean_ctor_set(v___x_403_, 0, v___x_419_);
v___x_421_ = v___x_403_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_423_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v_c_392_);
v___x_425_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = l_Lean_MessageData_ofName(v_mod_408_);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = l_Lean_MessageData_note(v___x_430_);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v_msg_375_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 0);
lean_ctor_set(v___x_403_, 0, v___x_432_);
v___x_434_ = v___x_403_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_437_; 
lean_dec_ref(v_env_380_);
lean_dec(v_declHint_376_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v_msg_375_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_438_, lean_object* v_declHint_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_438_, v_declHint_439_, v___y_440_);
lean_dec(v___y_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_443_, lean_object* v_declHint_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_458_; 
v___x_448_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_443_, v_declHint_444_, v___y_446_);
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_458_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_458_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_458_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_453_ = l_Lean_unknownIdentifierMessageTag;
v___x_454_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v_a_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_454_);
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_459_, lean_object* v_declHint_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_459_, v_declHint_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_465_, lean_object* v_msg_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_toCold_470_; lean_object* v_currRecDepth_471_; lean_object* v_ref_472_; uint8_t v_diag_473_; uint8_t v_suppressElabErrors_474_; lean_object* v_ref_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_toCold_470_ = lean_ctor_get(v___y_467_, 0);
v_currRecDepth_471_ = lean_ctor_get(v___y_467_, 1);
v_ref_472_ = lean_ctor_get(v___y_467_, 2);
v_diag_473_ = lean_ctor_get_uint8(v___y_467_, sizeof(void*)*3);
v_suppressElabErrors_474_ = lean_ctor_get_uint8(v___y_467_, sizeof(void*)*3 + 1);
v_ref_475_ = l_Lean_replaceRef(v_ref_465_, v_ref_472_);
lean_inc(v_currRecDepth_471_);
lean_inc_ref(v_toCold_470_);
v___x_476_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_476_, 0, v_toCold_470_);
lean_ctor_set(v___x_476_, 1, v_currRecDepth_471_);
lean_ctor_set(v___x_476_, 2, v_ref_475_);
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*3, v_diag_473_);
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*3 + 1, v_suppressElabErrors_474_);
v___x_477_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(v_msg_466_, v___x_476_, v___y_468_);
lean_dec_ref_known(v___x_476_, 3);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_478_, lean_object* v_msg_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_478_, v_msg_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v_ref_478_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_484_, lean_object* v_msg_485_, lean_object* v_declHint_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; lean_object* v_a_491_; lean_object* v___x_492_; 
v___x_490_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_485_, v_declHint_486_, v___y_487_, v___y_488_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref(v___x_490_);
v___x_492_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_484_, v_a_491_, v___y_487_, v___y_488_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_493_, lean_object* v_msg_494_, lean_object* v_declHint_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_493_, v_msg_494_, v_declHint_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v_ref_493_);
return v_res_499_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_506_, lean_object* v_constName_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___x_511_; uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_511_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_512_ = 0;
lean_inc(v_constName_507_);
v___x_513_ = l_Lean_MessageData_ofConstName(v_constName_507_, v___x_512_);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_511_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_506_, v___x_516_, v_constName_507_, v___y_508_, v___y_509_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_518_, lean_object* v_constName_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_518_, v_constName_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v_ref_518_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(lean_object* v_constName_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_ref_528_; lean_object* v___x_529_; 
v_ref_528_ = lean_ctor_get(v___y_525_, 2);
v___x_529_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_528_, v_constName_524_, v___y_525_, v___y_526_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(lean_object* v_constName_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___x_539_; lean_object* v_env_540_; uint8_t v___x_541_; lean_object* v___x_542_; 
v___x_539_ = lean_st_ref_get(v___y_537_);
v_env_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc_ref(v_env_540_);
lean_dec(v___x_539_);
v___x_541_ = 0;
lean_inc(v_constName_535_);
v___x_542_ = l_Lean_Environment_find_x3f(v_env_540_, v_constName_535_, v___x_541_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_535_, v___y_536_, v___y_537_);
return v___x_543_;
}
else
{
lean_object* v_val_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec(v_constName_535_);
v_val_544_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_542_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_val_544_);
lean_dec(v___x_542_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set_tag(v___x_546_, 0);
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_val_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0___boxed(lean_object* v_constName_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(v_constName_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_556_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__1(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__0));
v___x_559_ = l_Lean_stringToMessageData(v___x_558_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__8(void){
_start:
{
uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = 0;
v___x_572_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__7));
v___x_573_ = l_Lean_MessageData_ofConstName(v___x_572_, v___x_571_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__9(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__8, &l_Lean_Elab_checkCbvSimprocType___closed__8_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__8);
v___x_575_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__1, &l_Lean_Elab_checkCbvSimprocType___closed__1_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__1);
v___x_576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_574_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__11(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__10));
v___x_579_ = l_Lean_stringToMessageData(v___x_578_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__12(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__11, &l_Lean_Elab_checkCbvSimprocType___closed__11_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__11);
v___x_581_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__9, &l_Lean_Elab_checkCbvSimprocType___closed__9_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__9);
v___x_582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___x_580_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Elab_checkCbvSimprocType___closed__14(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__13));
v___x_585_ = l_Lean_stringToMessageData(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkCbvSimprocType(lean_object* v_declName_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_590_; 
lean_inc(v_declName_586_);
v___x_590_ = l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(v_declName_586_, v_a_587_, v_a_588_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_633_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_633_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_633_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_633_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___x_607_; 
v___x_607_ = l_Lean_ConstantInfo_type(v_a_591_);
if (lean_obj_tag(v___x_607_) == 4)
{
lean_object* v_declName_608_; 
v_declName_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_declName_608_);
lean_dec_ref_known(v___x_607_, 2);
if (lean_obj_tag(v_declName_608_) == 1)
{
lean_object* v_pre_609_; 
v_pre_609_ = lean_ctor_get(v_declName_608_, 0);
lean_inc(v_pre_609_);
if (lean_obj_tag(v_pre_609_) == 1)
{
lean_object* v_pre_610_; 
v_pre_610_ = lean_ctor_get(v_pre_609_, 0);
lean_inc(v_pre_610_);
if (lean_obj_tag(v_pre_610_) == 1)
{
lean_object* v_pre_611_; 
v_pre_611_ = lean_ctor_get(v_pre_610_, 0);
lean_inc(v_pre_611_);
if (lean_obj_tag(v_pre_611_) == 1)
{
lean_object* v_pre_612_; 
v_pre_612_ = lean_ctor_get(v_pre_611_, 0);
lean_inc(v_pre_612_);
if (lean_obj_tag(v_pre_612_) == 1)
{
lean_object* v_pre_613_; 
v_pre_613_ = lean_ctor_get(v_pre_612_, 0);
if (lean_obj_tag(v_pre_613_) == 0)
{
lean_object* v_str_614_; lean_object* v_str_615_; lean_object* v_str_616_; lean_object* v_str_617_; lean_object* v_str_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_str_614_ = lean_ctor_get(v_declName_608_, 1);
lean_inc_ref(v_str_614_);
lean_dec_ref_known(v_declName_608_, 2);
v_str_615_ = lean_ctor_get(v_pre_609_, 1);
lean_inc_ref(v_str_615_);
lean_dec_ref_known(v_pre_609_, 2);
v_str_616_ = lean_ctor_get(v_pre_610_, 1);
lean_inc_ref(v_str_616_);
lean_dec_ref_known(v_pre_610_, 2);
v_str_617_ = lean_ctor_get(v_pre_611_, 1);
lean_inc_ref(v_str_617_);
lean_dec_ref_known(v_pre_611_, 2);
v_str_618_ = lean_ctor_get(v_pre_612_, 1);
lean_inc_ref(v_str_618_);
lean_dec_ref_known(v_pre_612_, 2);
v___x_619_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__2));
v___x_620_ = lean_string_dec_eq(v_str_618_, v___x_619_);
lean_dec_ref(v_str_618_);
if (v___x_620_ == 0)
{
lean_dec_ref(v_str_617_);
lean_dec_ref(v_str_616_);
lean_dec_ref(v_str_615_);
lean_dec_ref(v_str_614_);
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
else
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__3));
v___x_622_ = lean_string_dec_eq(v_str_617_, v___x_621_);
lean_dec_ref(v_str_617_);
if (v___x_622_ == 0)
{
lean_dec_ref(v_str_616_);
lean_dec_ref(v_str_615_);
lean_dec_ref(v_str_614_);
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
else
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__4));
v___x_624_ = lean_string_dec_eq(v_str_616_, v___x_623_);
lean_dec_ref(v_str_616_);
if (v___x_624_ == 0)
{
lean_dec_ref(v_str_615_);
lean_dec_ref(v_str_614_);
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
else
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__5));
v___x_626_ = lean_string_dec_eq(v_str_615_, v___x_625_);
lean_dec_ref(v_str_615_);
if (v___x_626_ == 0)
{
lean_dec_ref(v_str_614_);
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
else
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__6));
v___x_628_ = lean_string_dec_eq(v_str_614_, v___x_627_);
lean_dec_ref(v_str_614_);
if (v___x_628_ == 0)
{
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_631_; 
lean_dec(v_a_591_);
lean_dec(v_declName_586_);
v___x_629_ = lean_box(0);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_629_);
v___x_631_ = v___x_593_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_612_, 2);
lean_dec_ref_known(v_pre_611_, 2);
lean_dec_ref_known(v_pre_610_, 2);
lean_dec_ref_known(v_pre_609_, 2);
lean_dec_ref_known(v_declName_608_, 2);
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
}
else
{
lean_dec_ref_known(v_pre_611_, 2);
lean_dec(v_pre_612_);
lean_dec_ref_known(v_pre_610_, 2);
lean_dec_ref_known(v_pre_609_, 2);
lean_dec_ref_known(v_declName_608_, 2);
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
}
else
{
lean_dec(v_pre_611_);
lean_dec_ref_known(v_pre_610_, 2);
lean_dec_ref_known(v_pre_609_, 2);
lean_dec_ref_known(v_declName_608_, 2);
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
}
else
{
lean_dec_ref_known(v_pre_609_, 2);
lean_dec(v_pre_610_);
lean_dec_ref_known(v_declName_608_, 2);
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
}
else
{
lean_dec(v_pre_609_);
lean_dec_ref_known(v_declName_608_, 2);
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
}
else
{
lean_dec(v_declName_608_);
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
}
else
{
lean_dec_ref(v___x_607_);
lean_del_object(v___x_593_);
v___y_596_ = v_a_587_;
v___y_597_ = v_a_588_;
goto v___jp_595_;
}
v___jp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_598_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__12, &l_Lean_Elab_checkCbvSimprocType___closed__12_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__12);
v___x_599_ = l_Lean_MessageData_ofName(v_declName_586_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_obj_once(&l_Lean_Elab_checkCbvSimprocType___closed__14, &l_Lean_Elab_checkCbvSimprocType___closed__14_once, _init_l_Lean_Elab_checkCbvSimprocType___closed__14);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_ConstantInfo_type(v_a_591_);
lean_dec(v_a_591_);
v___x_604_ = l_Lean_indentExpr(v___x_603_);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_602_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(v___x_605_, v___y_596_, v___y_597_);
return v___x_606_;
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v_declName_586_);
v_a_634_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_590_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_590_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkCbvSimprocType___boxed(lean_object* v_declName_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_checkCbvSimprocType(v_declName_642_, v_a_643_, v_a_644_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1(lean_object* v_00_u03b1_647_, lean_object* v_msg_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(v_msg_648_, v___y_649_, v___y_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___boxed(lean_object* v_00_u03b1_653_, lean_object* v_msg_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1(v_00_u03b1_653_, v_msg_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0(lean_object* v_00_u03b1_659_, lean_object* v_constName_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_660_, v___y_661_, v___y_662_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_665_, lean_object* v_constName_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0(v_00_u03b1_665_, v_constName_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_671_, lean_object* v_ref_672_, lean_object* v_constName_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_672_, v_constName_673_, v___y_674_, v___y_675_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_678_, lean_object* v_ref_679_, lean_object* v_constName_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1(v_00_u03b1_678_, v_ref_679_, v_constName_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v_ref_679_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_685_, lean_object* v_ref_686_, lean_object* v_msg_687_, lean_object* v_declHint_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_686_, v_msg_687_, v_declHint_688_, v___y_689_, v___y_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_693_, lean_object* v_ref_694_, lean_object* v_msg_695_, lean_object* v_declHint_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_693_, v_ref_694_, v_msg_695_, v_declHint_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v_ref_694_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_701_, lean_object* v_declHint_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_701_, v_declHint_702_, v___y_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_707_, lean_object* v_declHint_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_707_, v_declHint_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_713_, lean_object* v_ref_714_, lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_714_, v_msg_715_, v___y_716_, v___y_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_720_, lean_object* v_ref_721_, lean_object* v_msg_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_720_, v_ref_721_, v_msg_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v_ref_721_);
return v_res_726_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_box(0);
v___x_728_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg(){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___boxed(lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0(lean_object* v_00_u03b1_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___boxed(lean_object* v_00_u03b1_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0(v_00_u03b1_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0(lean_object* v___x_745_, lean_object* v___x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_realizeGlobalConstNoOverload(v___x_745_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc_n(v_a_755_, 2);
lean_dec_ref_known(v___x_754_, 1);
v___x_756_ = l_Lean_Elab_checkCbvSimprocType(v_a_755_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v___x_757_; 
lean_dec_ref_known(v___x_756_, 1);
v___x_757_ = l_Lean_Elab_elabCbvSimprocKeys(v___x_746_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(v_a_755_, v_a_758_, v___y_751_, v___y_752_);
return v___x_759_;
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_a_755_);
v_a_760_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_757_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_757_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_dec(v_a_755_);
lean_dec(v___x_746_);
return v___x_756_;
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v___x_746_);
v_a_768_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_754_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_754_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0___boxed(lean_object* v___x_776_, lean_object* v___x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0(v___x_776_, v___x_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern(lean_object* v_stx_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2));
lean_inc(v_stx_792_);
v___x_797_ = l_Lean_Syntax_isOfKind(v_stx_792_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec(v_stx_792_);
v___x_798_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
return v___x_798_;
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___f_803_; lean_object* v___x_804_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = l_Lean_Syntax_getArg(v_stx_792_, v___x_799_);
v___x_801_ = lean_unsigned_to_nat(3u);
v___x_802_ = l_Lean_Syntax_getArg(v_stx_792_, v___x_801_);
lean_dec(v_stx_792_);
v___f_803_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0___boxed), 9, 2);
lean_closure_set(v___f_803_, 0, v___x_802_);
lean_closure_set(v___f_803_, 1, v___x_800_);
v___x_804_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_803_, v_a_793_, v_a_794_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPattern___boxed(lean_object* v_stx_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Elab_Command_elabCbvSimprocPattern(v_stx_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1(){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_819_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_820_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2));
v___x_821_ = ((lean_object*)(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3));
v___x_822_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCbvSimprocPattern___boxed), 4, 0);
v___x_823_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_819_, v___x_820_, v___x_821_, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___boxed(lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1();
return v_res_825_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = lean_box(0);
v___x_836_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3));
v___x_837_ = l_Lean_mkConst(v___x_836_, v___x_835_);
return v___x_837_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_box(0);
v___x_846_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6));
v___x_847_ = l_Lean_mkConst(v___x_846_, v___x_845_);
return v___x_847_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_box(0);
v___x_856_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9));
v___x_857_ = l_Lean_mkConst(v___x_856_, v___x_855_);
return v___x_857_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_box(0);
v___x_865_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13));
v___x_866_ = l_Lean_mkConst(v___x_865_, v___x_864_);
return v___x_866_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_box(0);
v___x_873_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16));
v___x_874_ = l_Lean_mkConst(v___x_873_, v___x_872_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = lean_box(0);
v___x_883_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19));
v___x_884_ = l_Lean_mkConst(v___x_883_, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_box(0);
v___x_892_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23));
v___x_893_ = l_Lean_mkConst(v___x_892_, v___x_891_);
return v___x_893_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_box(0);
v___x_902_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26));
v___x_903_ = l_Lean_mkConst(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = lean_box(0);
v___x_912_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29));
v___x_913_ = l_Lean_mkConst(v___x_912_, v___x_911_);
return v___x_913_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_box(0);
v___x_922_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32));
v___x_923_ = l_Lean_mkConst(v___x_922_, v___x_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(lean_object* v_nilFn_924_, lean_object* v_consFn_925_, lean_object* v_x_926_){
_start:
{
if (lean_obj_tag(v_x_926_) == 0)
{
lean_dec_ref(v_consFn_925_);
lean_inc_ref(v_nilFn_924_);
return v_nilFn_924_;
}
else
{
lean_object* v_head_927_; lean_object* v_tail_928_; lean_object* v___y_930_; 
v_head_927_ = lean_ctor_get(v_x_926_, 0);
lean_inc(v_head_927_);
v_tail_928_ = lean_ctor_get(v_x_926_, 1);
lean_inc(v_tail_928_);
lean_dec_ref_known(v_x_926_, 2);
switch(lean_obj_tag(v_head_927_))
{
case 0:
{
lean_object* v___x_933_; 
v___x_933_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4);
v___y_930_ = v___x_933_;
goto v___jp_929_;
}
case 1:
{
lean_object* v___x_934_; 
v___x_934_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7);
v___y_930_ = v___x_934_;
goto v___jp_929_;
}
case 2:
{
lean_object* v_a_935_; lean_object* v___x_936_; 
v_a_935_ = lean_ctor_get(v_head_927_, 0);
lean_inc_ref(v_a_935_);
lean_dec_ref_known(v_head_927_, 1);
v___x_936_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10);
if (lean_obj_tag(v_a_935_) == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_937_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14);
v___x_938_ = l_Lean_Expr_lit___override(v_a_935_);
v___x_939_ = l_Lean_Expr_app___override(v___x_937_, v___x_938_);
v___x_940_ = l_Lean_Expr_app___override(v___x_936_, v___x_939_);
v___y_930_ = v___x_940_;
goto v___jp_929_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_941_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17);
v___x_942_ = l_Lean_Expr_lit___override(v_a_935_);
v___x_943_ = l_Lean_Expr_app___override(v___x_941_, v___x_942_);
v___x_944_ = l_Lean_Expr_app___override(v___x_936_, v___x_943_);
v___y_930_ = v___x_944_;
goto v___jp_929_;
}
}
case 3:
{
lean_object* v_a_945_; lean_object* v_a_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_a_945_ = lean_ctor_get(v_head_927_, 0);
lean_inc(v_a_945_);
v_a_946_ = lean_ctor_get(v_head_927_, 1);
lean_inc(v_a_946_);
lean_dec_ref_known(v_head_927_, 2);
v___x_947_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20);
v___x_948_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24);
v___x_949_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_945_);
v___x_950_ = l_Lean_Expr_app___override(v___x_948_, v___x_949_);
v___x_951_ = l_Lean_mkNatLit(v_a_946_);
v___x_952_ = l_Lean_mkAppB(v___x_947_, v___x_950_, v___x_951_);
v___y_930_ = v___x_952_;
goto v___jp_929_;
}
case 4:
{
lean_object* v_a_953_; lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_a_953_ = lean_ctor_get(v_head_927_, 0);
lean_inc(v_a_953_);
v_a_954_ = lean_ctor_get(v_head_927_, 1);
lean_inc(v_a_954_);
lean_dec_ref_known(v_head_927_, 2);
v___x_955_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27);
v___x_956_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_953_);
v___x_957_ = l_Lean_mkNatLit(v_a_954_);
v___x_958_ = l_Lean_mkAppB(v___x_955_, v___x_956_, v___x_957_);
v___y_930_ = v___x_958_;
goto v___jp_929_;
}
case 5:
{
lean_object* v___x_959_; 
v___x_959_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30);
v___y_930_ = v___x_959_;
goto v___jp_929_;
}
default: 
{
lean_object* v_a_960_; lean_object* v_a_961_; lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_a_960_ = lean_ctor_get(v_head_927_, 0);
lean_inc(v_a_960_);
v_a_961_ = lean_ctor_get(v_head_927_, 1);
lean_inc(v_a_961_);
v_a_962_ = lean_ctor_get(v_head_927_, 2);
lean_inc(v_a_962_);
lean_dec_ref_known(v_head_927_, 3);
v___x_963_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33);
v___x_964_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_960_);
v___x_965_ = l_Lean_mkNatLit(v_a_961_);
v___x_966_ = l_Lean_mkNatLit(v_a_962_);
v___x_967_ = l_Lean_mkApp3(v___x_963_, v___x_964_, v___x_965_, v___x_966_);
v___y_930_ = v___x_967_;
goto v___jp_929_;
}
}
v___jp_929_:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_inc_ref(v_consFn_925_);
v___x_931_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nilFn_924_, v_consFn_925_, v_tail_928_);
v___x_932_ = l_Lean_mkAppB(v_consFn_925_, v___y_930_, v___x_931_);
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___boxed(lean_object* v_nilFn_968_, lean_object* v_consFn_969_, lean_object* v_x_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nilFn_968_, v_consFn_969_, v_x_970_);
lean_dec_ref(v_nilFn_968_);
return v_res_971_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6));
v___x_984_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5));
v___x_985_ = l_Lean_mkConst(v___x_984_, v___x_983_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6));
v___x_994_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11));
v___x_995_ = l_Lean_mkConst(v___x_994_, v___x_993_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6));
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14));
v___x_1002_ = l_Lean_mkConst(v___x_1001_, v___x_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0(lean_object* v___x_1003_, lean_object* v___x_1004_, lean_object* v___x_1005_, lean_object* v___x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_realizeGlobalConstNoOverload(v___x_1003_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc_n(v_a_1015_, 2);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = l_Lean_Elab_checkCbvSimprocType(v_a_1015_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v___x_1017_; 
lean_dec_ref_known(v___x_1016_, 1);
v___x_1017_ = l_Lean_Elab_elabCbvSimprocKeys(v___x_1004_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__3));
v___x_1020_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0));
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1));
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2));
lean_inc_ref(v___x_1005_);
v___x_1023_ = l_Lean_Name_mkStr5(v___x_1005_, v___x_1019_, v___x_1020_, v___x_1021_, v___x_1022_);
v___x_1024_ = lean_box(0);
v___x_1025_ = l_Lean_mkConst(v___x_1023_, v___x_1024_);
lean_inc_n(v_a_1015_, 2);
v___x_1026_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_1015_);
v___x_1027_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0));
v___x_1028_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1));
v___x_1029_ = l_Lean_Name_mkStr4(v___x_1005_, v___x_1019_, v___x_1027_, v___x_1028_);
v___x_1030_ = l_Lean_mkConst(v___x_1029_, v___x_1024_);
v___x_1031_ = lean_obj_once(&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7, &l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7_once, _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7);
v___x_1032_ = l_Lean_mkConst(v_a_1015_, v___x_1024_);
v___x_1033_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9));
v___x_1034_ = l_Lean_Name_append(v_a_1015_, v___x_1033_);
v___x_1035_ = l_Lean_Core_mkFreshUserName(v___x_1034_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; lean_object* v_nil_1038_; lean_object* v___x_1039_; lean_object* v_cons_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = lean_obj_once(&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12, &l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_once, _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12);
lean_inc_ref_n(v___x_1030_, 2);
v_nil_1038_ = l_Lean_Expr_app___override(v___x_1037_, v___x_1030_);
v___x_1039_ = lean_obj_once(&l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15, &l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15_once, _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15);
v_cons_1040_ = l_Lean_Expr_app___override(v___x_1039_, v___x_1030_);
v___x_1041_ = lean_array_to_list(v_a_1018_);
v___x_1042_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nil_1038_, v_cons_1040_, v___x_1041_);
lean_dec_ref(v_nil_1038_);
v___x_1043_ = l_Lean_mkAppB(v___x_1031_, v___x_1030_, v___x_1042_);
v___x_1044_ = lean_mk_empty_array_with_capacity(v___x_1006_);
v___x_1045_ = lean_array_push(v___x_1044_, v___x_1026_);
v___x_1046_ = lean_array_push(v___x_1045_, v___x_1043_);
v___x_1047_ = lean_array_push(v___x_1046_, v___x_1032_);
v___x_1048_ = l_Lean_mkAppN(v___x_1025_, v___x_1047_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = l_Lean_declareBuiltin(v_a_1036_, v___x_1048_, v___y_1011_, v___y_1012_);
return v___x_1049_;
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v___x_1026_);
lean_dec_ref(v___x_1025_);
lean_dec(v_a_1018_);
v_a_1050_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1035_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1035_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v_a_1015_);
lean_dec_ref(v___x_1005_);
v_a_1058_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1017_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1017_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_dec(v_a_1015_);
lean_dec_ref(v___x_1005_);
lean_dec(v___x_1004_);
return v___x_1016_;
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v___x_1005_);
lean_dec(v___x_1004_);
v_a_1066_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1014_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1014_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___boxed(lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v___x_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0(v___x_1074_, v___x_1075_, v___x_1076_, v___x_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___x_1077_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin(lean_object* v_stx_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1095_ = ((lean_object*)(l_Lean_Elab_checkCbvSimprocType___closed__2));
v___x_1096_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1));
lean_inc(v_stx_1091_);
v___x_1097_ = l_Lean_Syntax_isOfKind(v_stx_1091_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_dec(v_stx_1091_);
v___x_1098_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; 
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = l_Lean_Syntax_getArg(v_stx_1091_, v___x_1099_);
v___x_1101_ = lean_unsigned_to_nat(3u);
v___x_1102_ = l_Lean_Syntax_getArg(v_stx_1091_, v___x_1101_);
lean_dec(v_stx_1091_);
v___f_1103_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1103_, 0, v___x_1102_);
lean_closure_set(v___f_1103_, 1, v___x_1100_);
lean_closure_set(v___f_1103_, 2, v___x_1095_);
lean_closure_set(v___f_1103_, 3, v___x_1101_);
v___x_1104_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1103_, v_a_1092_, v_a_1093_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___boxed(lean_object* v_stx_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin(v_stx_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1(){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1117_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1118_ = ((lean_object*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1));
v___x_1119_ = ((lean_object*)(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1));
v___x_1120_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___boxed), 4, 0);
v___x_1121_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1117_, v___x_1118_, v___x_1119_, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___boxed(lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1();
return v_res_1123_;
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
