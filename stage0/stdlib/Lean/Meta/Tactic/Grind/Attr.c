// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Attr
// Imports: public import Lean.Meta.Tactic.Grind.Injective public import Lean.Meta.Tactic.Grind.Cases public import Lean.Meta.Tactic.Grind.ExtAttr public import Lean.Meta.Tactic.Simp.Attr public import Lean.Meta.Tactic.Grind.Homo public import Lean.Meta.Sym.DSimp.Rewrite import Lean.Meta.Sym.Simp.Attr import Lean.ExtraModUses
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_mkExtension(lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Meta_addDeclToUnfold(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_Decls_addEntry(lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Sym_DSimp_Decls_mkEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateExtAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSymbolPriorityAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpTheoremFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default;
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "normExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 117, 24, 11, 244, 218, 170, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normExt;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "norm"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 82, 242, 154, 5, 26, 236, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 98, 249, 2, 230, 183, 10, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 254, 122, 13, 209, 4, 96, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(88, 171, 221, 227, 25, 133, 195, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 72, 241, 93, 31, 88, 24, 156)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 99, 64, 101, 196, 242, 78, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 102, 233, 244, 63, 110, 171, 66)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 38, 22, 238, 56, 195, 101, 225)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 32, 197, 231, 9, 105, 134, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 8, 248, 216, 120, 97, 211, 252)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 115, 203, 254, 31, 135, 121, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 182, 250, 113, 105, 31, 65, 165)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 202, 156, 167, 66, 153, 39, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 187, 236, 120, 172, 89, 32, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(448808965) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(24, 160, 99, 55, 202, 33, 244, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 159, 216, 39, 51, 61, 141, 72)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 73, 198, 215, 12, 41, 81, 204)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(146, 108, 201, 9, 220, 24, 56, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymEntry_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymEntry;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymTheorems_addEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_NormSymEntry_declName_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "normSymExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 33, 18, 12, 138, 185, 216, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_NormSymTheorems_addEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSymExt;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "skipping `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`, not a global declaration"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "skipping unfold `"};
static const lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "unexpected `grind` theorem kind: `"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__4;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__6;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindEq"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(179, 34, 219, 24, 240, 38, 65, 204)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindDef"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value),LEAN_SCALAR_PTR_LITERAL(66, 218, 12, 28, 39, 29, 4, 77)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindFwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value),LEAN_SCALAR_PTR_LITERAL(121, 161, 177, 116, 112, 162, 92, 47)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value),LEAN_SCALAR_PTR_LITERAL(114, 163, 57, 243, 160, 41, 114, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqRhs"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value),LEAN_SCALAR_PTR_LITERAL(222, 187, 148, 221, 105, 213, 199, 68)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindEqBoth"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value),LEAN_SCALAR_PTR_LITERAL(79, 230, 133, 190, 186, 228, 109, 128)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value),LEAN_SCALAR_PTR_LITERAL(250, 57, 23, 180, 238, 116, 90, 53)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindLR"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value),LEAN_SCALAR_PTR_LITERAL(152, 111, 188, 78, 132, 212, 97, 164)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindRL"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value),LEAN_SCALAR_PTR_LITERAL(84, 112, 237, 169, 105, 148, 42, 205)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindUsr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value),LEAN_SCALAR_PTR_LITERAL(204, 58, 160, 148, 192, 167, 114, 18)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindGen"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value),LEAN_SCALAR_PTR_LITERAL(186, 203, 120, 147, 97, 215, 208, 134)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindCases"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value),LEAN_SCALAR_PTR_LITERAL(85, 142, 28, 230, 49, 50, 229, 162)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grindCasesEager"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value),LEAN_SCALAR_PTR_LITERAL(75, 210, 92, 40, 190, 183, 142, 70)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindIntro"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value),LEAN_SCALAR_PTR_LITERAL(142, 126, 114, 89, 237, 253, 56, 138)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindExt"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value),LEAN_SCALAR_PTR_LITERAL(147, 193, 153, 166, 243, 149, 163, 253)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindInj"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 41, 9, 21, 5, 145, 193)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindFunCC"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value),LEAN_SCALAR_PTR_LITERAL(217, 20, 186, 134, 249, 79, 78, 43)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindNorm"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value),LEAN_SCALAR_PTR_LITERAL(166, 126, 146, 239, 104, 253, 29, 148)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindUnfold"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value),LEAN_SCALAR_PTR_LITERAL(214, 181, 37, 92, 122, 232, 164, 219)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindHom"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value),LEAN_SCALAR_PTR_LITERAL(14, 226, 234, 13, 148, 139, 225, 180)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grindHomFallback"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value),LEAN_SCALAR_PTR_LITERAL(140, 210, 151, 50, 71, 98, 251, 189)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindHomPred"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value),LEAN_SCALAR_PTR_LITERAL(1, 153, 163, 64, 153, 27, 218, 140)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__51 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "priority expected"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__54;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__55 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__58 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__59 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__60 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__61 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__62 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__63 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__63_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__64 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__65 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__65_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "the modifier `usr` is only relevant in parameters for `grind only`"};
static const lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "\?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "]` instead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "cannot mark declaration to be unfolded by `grind`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "invalid `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " intro]`, `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "symbol priorities must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "normalizer must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "declaration to unfold must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "homomorphism rules must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "homomorphism predicates must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "When applied to an equational theorem, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " =]`, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " =_]`, or `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = " _=_]`will mark the theorem for use in heuristic instantiations by the `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 135, .m_data = "` tactic,\n      using respectively the left-hand side, the right-hand side, or both sides of the theorem.When applied to a function, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 112, .m_capacity = 112, .m_length = 111, .m_data = " =]` automatically annotates the equational theorems associated with that function.When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 183, .m_capacity = 183, .m_length = 180, .m_data = " ←]` will instantiate the theorem whenever it encounters the conclusion of the theorem\n      (that is, it will use the theorem for backwards reasoning).When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 190, .m_capacity = 190, .m_length = 187, .m_data = " →]` will instantiate the theorem whenever it encounters sufficiently many of the propositional hypotheses\n      (that is, it will use the theorem for forwards reasoning).The attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "]` by itself will effectively try `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 68, .m_data = " ←]` (if the conclusion is sufficient for instantiation) and then `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 162, .m_data = " →]`.The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.For example, if a theorem `@["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 179, .m_capacity = 179, .m_length = 178, .m_data = " =] theorem foo_idempotent : foo (foo x) = foo x` is annotated,`grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "The `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "]` attribute is used to annotate declarations."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "!]` attribute is used to annotate declarations, but selecting minimal indexable subterms."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "!\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "!]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_extensionMapRef;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___auto__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value),LEAN_SCALAR_PTR_LITERAL(160, 1, 171, 211, 177, 132, 129, 49)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_grindExt;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 161, 226, 116, 111, 153, 146, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "liaExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 224, 62, 90, 13, 174, 224, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liaExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_mkSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_94_ = 0;
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_96_ = l_Lean_registerTraceClass(v___x_93_, v___x_94_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2____boxed(lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_();
return v_res_98_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = l_Lean_NameSet_empty;
v___x_105_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3);
v___x_108_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2);
v___x_109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
lean_ctor_set(v___x_109_, 2, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default;
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl(lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_tag_nat(v_x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl___boxed(lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl(v_x_114_);
lean_dec_ref(v_x_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(lean_object* v_t_116_, lean_object* v_k_117_){
_start:
{
lean_object* v_thm_118_; lean_object* v___x_119_; 
v_thm_118_ = lean_ctor_get(v_t_116_, 0);
lean_inc_ref(v_thm_118_);
lean_dec_ref(v_t_116_);
v___x_119_ = lean_apply_1(v_k_117_, v_thm_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim(lean_object* v_motive_120_, lean_object* v_ctorIdx_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_k_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_122_, v_k_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___boxed(lean_object* v_motive_126_, lean_object* v_ctorIdx_127_, lean_object* v_t_128_, lean_object* v_h_129_, lean_object* v_k_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim(v_motive_126_, v_ctorIdx_127_, v_t_128_, v_h_129_, v_k_130_);
lean_dec(v_ctorIdx_127_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim___redArg(lean_object* v_t_132_, lean_object* v_pre_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_132_, v_pre_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim(lean_object* v_motive_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_pre_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_136_, v_pre_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim___redArg(lean_object* v_t_140_, lean_object* v_post_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_140_, v_post_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim(lean_object* v_motive_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_post_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_144_, v_post_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim___redArg(lean_object* v_t_148_, lean_object* v_dsimp_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_148_, v_dsimp_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim(lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_dsimp_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_152_, v_dsimp_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default;
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry(void){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Meta_Grind_instInhabitedNormSymEntry_default;
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymTheorems_addEntry(lean_object* v_s_160_, lean_object* v_x_161_){
_start:
{
switch(lean_obj_tag(v_x_161_))
{
case 0:
{
lean_object* v_thm_162_; lean_object* v_pre_163_; lean_object* v_post_164_; lean_object* v_dsimp_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_173_; 
v_thm_162_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_thm_162_);
lean_dec_ref_known(v_x_161_, 1);
v_pre_163_ = lean_ctor_get(v_s_160_, 0);
v_post_164_ = lean_ctor_get(v_s_160_, 1);
v_dsimp_165_ = lean_ctor_get(v_s_160_, 2);
v_isSharedCheck_173_ = !lean_is_exclusive(v_s_160_);
if (v_isSharedCheck_173_ == 0)
{
v___x_167_ = v_s_160_;
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_dsimp_165_);
lean_inc(v_post_164_);
lean_inc(v_pre_163_);
lean_dec(v_s_160_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_pre_163_, v_thm_162_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_post_164_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_dsimp_165_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
case 1:
{
lean_object* v_thm_174_; lean_object* v_pre_175_; lean_object* v_post_176_; lean_object* v_dsimp_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_185_; 
v_thm_174_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_thm_174_);
lean_dec_ref_known(v_x_161_, 1);
v_pre_175_ = lean_ctor_get(v_s_160_, 0);
v_post_176_ = lean_ctor_get(v_s_160_, 1);
v_dsimp_177_ = lean_ctor_get(v_s_160_, 2);
v_isSharedCheck_185_ = !lean_is_exclusive(v_s_160_);
if (v_isSharedCheck_185_ == 0)
{
v___x_179_ = v_s_160_;
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_dsimp_177_);
lean_inc(v_post_176_);
lean_inc(v_pre_175_);
lean_dec(v_s_160_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_post_176_, v_thm_174_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_181_);
v___x_183_ = v___x_179_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_pre_175_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_dsimp_177_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
default: 
{
lean_object* v_entry_186_; lean_object* v_pre_187_; lean_object* v_post_188_; lean_object* v_dsimp_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_197_; 
v_entry_186_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_entry_186_);
lean_dec_ref_known(v_x_161_, 1);
v_pre_187_ = lean_ctor_get(v_s_160_, 0);
v_post_188_ = lean_ctor_get(v_s_160_, 1);
v_dsimp_189_ = lean_ctor_get(v_s_160_, 2);
v_isSharedCheck_197_ = !lean_is_exclusive(v_s_160_);
if (v_isSharedCheck_197_ == 0)
{
v___x_191_ = v_s_160_;
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_dsimp_189_);
lean_inc(v_post_188_);
lean_inc(v_pre_187_);
lean_dec(v_s_160_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = l_Lean_Meta_Sym_DSimp_Decls_addEntry(v_dsimp_189_, v_entry_186_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 2, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_pre_187_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_post_188_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_NormSymEntry_declName_x3f(lean_object* v_x_198_){
_start:
{
lean_object* v_thm_200_; 
if (lean_obj_tag(v_x_198_) == 2)
{
lean_object* v_entry_205_; 
v_entry_205_ = lean_ctor_get(v_x_198_, 0);
lean_inc_ref(v_entry_205_);
lean_dec_ref_known(v_x_198_, 1);
if (lean_obj_tag(v_entry_205_) == 0)
{
lean_object* v_thm_206_; 
v_thm_206_ = lean_ctor_get(v_entry_205_, 0);
lean_inc_ref(v_thm_206_);
lean_dec_ref_known(v_entry_205_, 1);
v_thm_200_ = v_thm_206_;
goto v___jp_199_;
}
else
{
lean_object* v_declName_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_declName_207_ = lean_ctor_get(v_entry_205_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_entry_205_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v_entry_205_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_declName_207_);
lean_dec(v_entry_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_declName_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v_thm_215_; 
v_thm_215_ = lean_ctor_get(v_x_198_, 0);
lean_inc_ref(v_thm_215_);
lean_dec_ref(v_x_198_);
v_thm_200_ = v_thm_215_;
goto v___jp_199_;
}
v___jp_199_:
{
lean_object* v_expr_201_; 
v_expr_201_ = lean_ctor_get(v_thm_200_, 0);
lean_inc_ref(v_expr_201_);
lean_dec_ref(v_thm_200_);
if (lean_obj_tag(v_expr_201_) == 4)
{
lean_object* v_declName_202_; lean_object* v___x_203_; 
v_declName_202_ = lean_ctor_get(v_expr_201_, 0);
lean_inc(v_declName_202_);
lean_dec_ref_known(v_expr_201_, 2);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v_declName_202_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; 
lean_dec_ref(v_expr_201_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object* v_x_216_, lean_object* v_e_217_){
_start:
{
lean_object* v___x_218_; 
lean_inc_ref(v_e_217_);
v___x_218_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_NormSymEntry_declName_x3f(v_e_217_);
if (lean_obj_tag(v___x_218_) == 1)
{
lean_object* v_val_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_233_; 
v_val_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_233_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_233_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_val_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_233_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint8_t v___x_223_; 
v___x_223_ = l_Lean_isPrivateName(v_val_219_);
lean_dec(v_val_219_);
if (v___x_223_ == 0)
{
lean_object* v___x_225_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_e_217_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_e_217_);
v___x_225_ = v_reuseFailAlloc_227_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; 
lean_inc_ref_n(v___x_225_, 2);
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
lean_ctor_set(v___x_226_, 2, v___x_225_);
return v___x_226_;
}
}
else
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_box(0);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_e_217_);
v___x_230_ = v___x_221_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_e_217_);
v___x_230_ = v_reuseFailAlloc_232_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_228_);
lean_ctor_set(v___x_231_, 1, v___x_228_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
return v___x_231_;
}
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v___x_218_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v_e_217_);
lean_inc_ref_n(v___x_234_, 2);
v___x_235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v_x_236_, lean_object* v_e_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(v_x_236_, v_e_237_);
lean_dec_ref(v_x_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object* v___y_239_){
_start:
{
lean_inc_ref(v___y_239_);
return v___y_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(v___y_240_);
lean_dec_ref(v___y_240_);
return v_res_241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_251_ = lean_box(0);
v___x_252_ = 0;
v___f_253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___f_254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_255_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4);
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_258_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
lean_ctor_set(v___x_258_, 2, v___x_256_);
lean_ctor_set(v___x_258_, 3, v___x_255_);
lean_ctor_set(v___x_258_, 4, v___f_254_);
lean_ctor_set(v___x_258_, 5, v___f_253_);
lean_ctor_set(v___x_258_, 6, v___x_251_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*7, v___x_252_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*7 + 1, v___x_252_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_);
v___x_261_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_();
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(lean_object* v_____r_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0));
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___boxed(lean_object* v_____r_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v_____r_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(lean_object* v_msgData_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_env_288_; uint8_t v___x_289_; lean_object* v_env_290_; lean_object* v___x_291_; lean_object* v_toCold_292_; lean_object* v_mctx_293_; lean_object* v_lctx_294_; lean_object* v_options_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_287_ = lean_st_ref_get(v___y_285_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc_ref(v_env_288_);
lean_dec(v___x_287_);
v___x_289_ = 0;
v_env_290_ = l_Lean_Environment_setRecordingDeps(v_env_288_, v___x_289_);
v___x_291_ = lean_st_ref_get(v___y_283_);
v_toCold_292_ = lean_ctor_get(v___y_284_, 0);
v_mctx_293_ = lean_ctor_get(v___x_291_, 0);
lean_inc_ref(v_mctx_293_);
lean_dec(v___x_291_);
v_lctx_294_ = lean_ctor_get(v___y_282_, 2);
v_options_295_ = lean_ctor_get(v_toCold_292_, 2);
lean_inc_ref(v_options_295_);
lean_inc_ref(v_lctx_294_);
v___x_296_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_296_, 0, v_env_290_);
lean_ctor_set(v___x_296_, 1, v_mctx_293_);
lean_ctor_set(v___x_296_, 2, v_lctx_294_);
lean_ctor_set(v___x_296_, 3, v_options_295_);
v___x_297_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_msgData_281_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msgData_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_305_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_306_; double v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_float_of_nat(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(lean_object* v_cls_311_, lean_object* v_msg_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_ref_318_; lean_object* v___x_319_; lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_365_; 
v_ref_318_ = lean_ctor_get(v___y_315_, 2);
v___x_319_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msg_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_365_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_365_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_365_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v_traceState_325_; lean_object* v_env_326_; lean_object* v_nextMacroScope_327_; lean_object* v_ngen_328_; lean_object* v_auxDeclNGen_329_; lean_object* v_cache_330_; lean_object* v_recordedDeps_331_; lean_object* v_messages_332_; lean_object* v_infoState_333_; lean_object* v_snapshotTasks_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_364_; 
v___x_324_ = lean_st_ref_take(v___y_316_);
v_traceState_325_ = lean_ctor_get(v___x_324_, 4);
v_env_326_ = lean_ctor_get(v___x_324_, 0);
v_nextMacroScope_327_ = lean_ctor_get(v___x_324_, 1);
v_ngen_328_ = lean_ctor_get(v___x_324_, 2);
v_auxDeclNGen_329_ = lean_ctor_get(v___x_324_, 3);
v_cache_330_ = lean_ctor_get(v___x_324_, 5);
v_recordedDeps_331_ = lean_ctor_get(v___x_324_, 6);
v_messages_332_ = lean_ctor_get(v___x_324_, 7);
v_infoState_333_ = lean_ctor_get(v___x_324_, 8);
v_snapshotTasks_334_ = lean_ctor_get(v___x_324_, 9);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_364_ == 0)
{
v___x_336_ = v___x_324_;
v_isShared_337_ = v_isSharedCheck_364_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snapshotTasks_334_);
lean_inc(v_infoState_333_);
lean_inc(v_messages_332_);
lean_inc(v_recordedDeps_331_);
lean_inc(v_cache_330_);
lean_inc(v_traceState_325_);
lean_inc(v_auxDeclNGen_329_);
lean_inc(v_ngen_328_);
lean_inc(v_nextMacroScope_327_);
lean_inc(v_env_326_);
lean_dec(v___x_324_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_364_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
uint64_t v_tid_338_; lean_object* v_traces_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_363_; 
v_tid_338_ = lean_ctor_get_uint64(v_traceState_325_, sizeof(void*)*1);
v_traces_339_ = lean_ctor_get(v_traceState_325_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_traceState_325_);
if (v_isSharedCheck_363_ == 0)
{
v___x_341_ = v_traceState_325_;
v_isShared_342_ = v_isSharedCheck_363_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_traces_339_);
lean_dec(v_traceState_325_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_363_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_344_; double v___x_345_; uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_343_ = lean_box(0);
v___x_344_ = lean_box(0);
v___x_345_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0);
v___x_346_ = 0;
v___x_347_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_348_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_348_, 0, v_cls_311_);
lean_ctor_set(v___x_348_, 1, v___x_344_);
lean_ctor_set(v___x_348_, 2, v___x_347_);
lean_ctor_set_float(v___x_348_, sizeof(void*)*3, v___x_345_);
lean_ctor_set_float(v___x_348_, sizeof(void*)*3 + 8, v___x_345_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*3 + 16, v___x_346_);
v___x_349_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2));
v___x_350_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v_a_320_);
lean_ctor_set(v___x_350_, 2, v___x_349_);
lean_inc(v_ref_318_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_ref_318_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = l_Lean_PersistentArray_push___redArg(v_traces_339_, v___x_351_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_352_);
v___x_354_ = v___x_341_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_352_);
lean_ctor_set_uint64(v_reuseFailAlloc_362_, sizeof(void*)*1, v_tid_338_);
v___x_354_ = v_reuseFailAlloc_362_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 4, v___x_354_);
v___x_356_ = v___x_336_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_env_326_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_nextMacroScope_327_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_ngen_328_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_auxDeclNGen_329_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_361_, 5, v_cache_330_);
lean_ctor_set(v_reuseFailAlloc_361_, 6, v_recordedDeps_331_);
lean_ctor_set(v_reuseFailAlloc_361_, 7, v_messages_332_);
lean_ctor_set(v_reuseFailAlloc_361_, 8, v_infoState_333_);
lean_ctor_set(v_reuseFailAlloc_361_, 9, v_snapshotTasks_334_);
v___x_356_ = v_reuseFailAlloc_361_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = lean_st_ref_put(v___y_316_, v___x_356_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_343_);
v___x_359_ = v___x_322_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_343_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___boxed(lean_object* v_cls_366_, lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_366_, v_msg_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1));
v___x_379_ = l_Lean_Name_append(v___x_378_, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(lean_object* v_thm_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___y_396_; lean_object* v_proof_409_; 
v_proof_409_ = lean_ctor_get(v_thm_389_, 2);
if (lean_obj_tag(v_proof_409_) == 4)
{
lean_object* v_declName_410_; lean_object* v___x_414_; 
lean_inc_ref(v_proof_409_);
lean_dec_ref(v_thm_389_);
v_declName_410_ = lean_ctor_get(v_proof_409_, 0);
lean_inc_n(v_declName_410_, 2);
lean_dec_ref_known(v_proof_409_, 2);
v___x_414_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_410_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_declName_410_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_423_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_a_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_419_);
v___x_421_ = v___x_417_;
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
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_461_; 
v_a_424_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_461_ == 0)
{
v___x_426_ = v___x_414_;
v_isShared_427_ = v_isSharedCheck_461_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_414_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_461_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint8_t v___x_428_; 
v___x_428_ = l_Lean_Exception_isInterrupt(v_a_424_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
lean_inc(v_a_424_);
v___x_429_ = l_Lean_Exception_isRuntime(v_a_424_);
if (v___x_429_ == 0)
{
lean_object* v_toCold_430_; lean_object* v_options_431_; uint8_t v_hasTrace_432_; 
lean_del_object(v___x_426_);
v_toCold_430_ = lean_ctor_get(v_a_392_, 0);
v_options_431_ = lean_ctor_get(v_toCold_430_, 2);
v_hasTrace_432_ = lean_ctor_get_uint8(v_options_431_, sizeof(void*)*1);
if (v_hasTrace_432_ == 0)
{
lean_dec(v_a_424_);
lean_dec(v_declName_410_);
goto v___jp_411_;
}
else
{
lean_object* v_inheritedTraceOptions_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_inheritedTraceOptions_433_ = lean_ctor_get(v_toCold_430_, 11);
v___x_434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_436_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_433_, v_options_431_, v___x_435_);
if (v___x_436_ == 0)
{
lean_dec(v_a_424_);
lean_dec(v_declName_410_);
goto v___jp_411_;
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_437_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4);
v___x_438_ = l_Lean_MessageData_ofConstName(v_declName_410_, v___x_429_);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = l_Lean_Exception_toMessageData(v_a_424_);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v___x_434_, v___x_443_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v___x_446_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v_a_445_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
v___y_396_ = v___x_446_;
goto v___jp_395_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_a_447_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_444_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_444_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v_declName_410_);
if (v_isShared_427_ == 0)
{
v___x_456_ = v___x_426_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_424_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v_declName_410_);
if (v_isShared_427_ == 0)
{
v___x_459_ = v___x_426_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_424_);
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
v___jp_411_:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_box(0);
v___x_413_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v___x_412_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
v___y_396_ = v___x_413_;
goto v___jp_395_;
}
}
else
{
lean_object* v_toCold_462_; lean_object* v_options_463_; uint8_t v_hasTrace_464_; 
v_toCold_462_ = lean_ctor_get(v_a_392_, 0);
v_options_463_ = lean_ctor_get(v_toCold_462_, 2);
v_hasTrace_464_ = lean_ctor_get_uint8(v_options_463_, sizeof(void*)*1);
if (v_hasTrace_464_ == 0)
{
lean_dec_ref(v_thm_389_);
goto v___jp_406_;
}
else
{
lean_object* v_origin_465_; lean_object* v_inheritedTraceOptions_466_; lean_object* v_cls_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_origin_465_ = lean_ctor_get(v_thm_389_, 4);
lean_inc_ref(v_origin_465_);
lean_dec_ref(v_thm_389_);
v_inheritedTraceOptions_466_ = lean_ctor_get(v_toCold_462_, 11);
v_cls_467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_468_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_469_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_466_, v_options_463_, v___x_468_);
if (v___x_469_ == 0)
{
lean_dec_ref(v_origin_465_);
goto v___jp_406_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_470_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4);
v___x_471_ = l_Lean_Meta_Origin_key(v_origin_465_);
lean_dec_ref(v_origin_465_);
v___x_472_ = l_Lean_MessageData_ofName(v___x_471_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_470_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8);
v___x_475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_467_, v___x_475_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_dec_ref_known(v___x_476_, 1);
goto v___jp_406_;
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
}
v___jp_395_:
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v_a_397_ = lean_ctor_get(v___y_396_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___y_396_);
if (v_isSharedCheck_405_ == 0)
{
v___x_399_ = v___y_396_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___y_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_a_401_; lean_object* v___x_403_; 
v_a_401_ = lean_ctor_get(v_a_397_, 0);
lean_inc(v_a_401_);
lean_dec(v_a_397_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v_a_401_);
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
v___jp_406_:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_box(0);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___boxed(lean_object* v_thm_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(v_thm_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
return v_res_491_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___dummy_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg();
return v_res_497_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg();
return v___x_502_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0);
v___x_507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
lean_ctor_set(v___x_507_, 2, v___x_505_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_508_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4);
v___x_509_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3);
v___x_510_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0);
v___x_511_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
v___x_512_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v___x_510_);
lean_ctor_set(v___x_512_, 2, v___x_509_);
lean_ctor_set(v___x_512_, 3, v___x_510_);
lean_ctor_set(v___x_512_, 4, v___x_510_);
lean_ctor_set(v___x_512_, 5, v___x_510_);
lean_ctor_set(v___x_512_, 6, v___x_510_);
lean_ctor_set(v___x_512_, 7, v___x_508_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(lean_object* v_ext_513_, lean_object* v_b_514_, uint8_t v_kind_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_toCold_520_; lean_object* v_currNamespace_521_; lean_object* v___x_522_; lean_object* v_env_523_; lean_object* v_nextMacroScope_524_; lean_object* v_ngen_525_; lean_object* v_auxDeclNGen_526_; lean_object* v_traceState_527_; lean_object* v_recordedDeps_528_; lean_object* v_messages_529_; lean_object* v_infoState_530_; lean_object* v_snapshotTasks_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_558_; 
v_toCold_520_ = lean_ctor_get(v___y_517_, 0);
v_currNamespace_521_ = lean_ctor_get(v_toCold_520_, 4);
v___x_522_ = lean_st_ref_take(v___y_518_);
v_env_523_ = lean_ctor_get(v___x_522_, 0);
v_nextMacroScope_524_ = lean_ctor_get(v___x_522_, 1);
v_ngen_525_ = lean_ctor_get(v___x_522_, 2);
v_auxDeclNGen_526_ = lean_ctor_get(v___x_522_, 3);
v_traceState_527_ = lean_ctor_get(v___x_522_, 4);
v_recordedDeps_528_ = lean_ctor_get(v___x_522_, 6);
v_messages_529_ = lean_ctor_get(v___x_522_, 7);
v_infoState_530_ = lean_ctor_get(v___x_522_, 8);
v_snapshotTasks_531_ = lean_ctor_get(v___x_522_, 9);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v___x_522_, 5);
lean_dec(v_unused_559_);
v___x_533_ = v___x_522_;
v_isShared_534_ = v_isSharedCheck_558_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snapshotTasks_531_);
lean_inc(v_infoState_530_);
lean_inc(v_messages_529_);
lean_inc(v_recordedDeps_528_);
lean_inc(v_traceState_527_);
lean_inc(v_auxDeclNGen_526_);
lean_inc(v_ngen_525_);
lean_inc(v_nextMacroScope_524_);
lean_inc(v_env_523_);
lean_dec(v___x_522_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_558_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
lean_inc(v_currNamespace_521_);
v___x_535_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_523_, v_ext_513_, v_b_514_, v_kind_515_, v_currNamespace_521_);
v___x_536_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 5, v___x_536_);
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_538_ = v___x_533_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_nextMacroScope_524_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_ngen_525_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_auxDeclNGen_526_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_traceState_527_);
lean_ctor_set(v_reuseFailAlloc_557_, 5, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_557_, 6, v_recordedDeps_528_);
lean_ctor_set(v_reuseFailAlloc_557_, 7, v_messages_529_);
lean_ctor_set(v_reuseFailAlloc_557_, 8, v_infoState_530_);
lean_ctor_set(v_reuseFailAlloc_557_, 9, v_snapshotTasks_531_);
v___x_538_ = v_reuseFailAlloc_557_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_mctx_541_; lean_object* v_zetaDeltaFVarIds_542_; lean_object* v_postponed_543_; lean_object* v_diag_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_555_; 
v___x_539_ = lean_st_ref_put(v___y_518_, v___x_538_);
v___x_540_ = lean_st_ref_take(v___y_516_);
v_mctx_541_ = lean_ctor_get(v___x_540_, 0);
v_zetaDeltaFVarIds_542_ = lean_ctor_get(v___x_540_, 2);
v_postponed_543_ = lean_ctor_get(v___x_540_, 3);
v_diag_544_ = lean_ctor_get(v___x_540_, 4);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v___x_540_, 1);
lean_dec(v_unused_556_);
v___x_546_ = v___x_540_;
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_diag_544_);
lean_inc(v_postponed_543_);
lean_inc(v_zetaDeltaFVarIds_542_);
lean_inc(v_mctx_541_);
lean_dec(v___x_540_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_548_ = lean_box(0);
v___x_549_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_549_);
v___x_551_ = v___x_546_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_mctx_541_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_zetaDeltaFVarIds_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_postponed_543_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_diag_544_);
v___x_551_ = v_reuseFailAlloc_554_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_st_ref_put(v___y_516_, v___x_551_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_548_);
return v___x_553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___boxed(lean_object* v_ext_560_, lean_object* v_b_561_, lean_object* v_kind_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
uint8_t v_kind_boxed_567_; lean_object* v_res_568_; 
v_kind_boxed_567_ = lean_unbox(v_kind_562_);
v_res_568_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v_ext_560_, v_b_561_, v_kind_boxed_567_, v___y_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(uint8_t v_attrKind_569_, uint8_t v_post_570_, lean_object* v_as_571_, size_t v_sz_572_, size_t v_i_573_, lean_object* v_b_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_a_581_; uint8_t v___x_585_; 
v___x_585_ = lean_usize_dec_lt(v_i_573_, v_sz_572_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v_b_574_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_587_ = lean_box(0);
v_a_588_ = lean_array_uget_borrowed(v_as_571_, v_i_573_);
v___x_589_ = l_Lean_Meta_Grind_normExt;
lean_inc(v_a_588_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v_a_588_);
v___x_591_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_589_, v___x_590_, v_attrKind_569_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_633_; 
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_634_);
v___x_593_ = v___x_591_;
v_isShared_594_ = v_isSharedCheck_633_;
goto v_resetjp_592_;
}
else
{
lean_dec(v___x_591_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_633_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; 
lean_inc(v_a_588_);
v___x_595_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(v_a_588_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
if (lean_obj_tag(v_a_596_) == 1)
{
lean_object* v_val_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_624_; 
v_val_597_ = lean_ctor_get(v_a_596_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_624_ == 0)
{
v___x_599_ = v_a_596_;
v_isShared_600_ = v_isSharedCheck_624_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_val_597_);
lean_dec(v_a_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_624_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___y_603_; 
v___x_601_ = l_Lean_Meta_Grind_normSymExt;
if (v_post_570_ == 0)
{
lean_object* v___x_619_; 
lean_inc(v_val_597_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v_val_597_);
v___x_619_ = v___x_593_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_val_597_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
v___y_603_ = v___x_619_;
goto v___jp_602_;
}
}
else
{
lean_object* v___x_622_; 
lean_inc(v_val_597_);
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 1);
lean_ctor_set(v___x_593_, 0, v_val_597_);
v___x_622_ = v___x_593_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_val_597_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
v___y_603_ = v___x_622_;
goto v___jp_602_;
}
}
v___jp_602_:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_601_, v___y_603_, v_attrKind_569_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_616_; 
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___x_604_, 0);
lean_dec(v_unused_617_);
v___x_606_ = v___x_604_;
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
else
{
lean_dec(v___x_604_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
if (v_post_570_ == 0)
{
lean_del_object(v___x_606_);
lean_del_object(v___x_599_);
lean_dec(v_val_597_);
v_a_581_ = v___x_587_;
goto v___jp_580_;
}
else
{
uint8_t v_rfl_608_; 
v_rfl_608_ = lean_ctor_get_uint8(v_a_588_, sizeof(void*)*5 + 2);
if (v_rfl_608_ == 0)
{
lean_del_object(v___x_606_);
lean_del_object(v___x_599_);
lean_dec(v_val_597_);
v_a_581_ = v___x_587_;
goto v___jp_580_;
}
else
{
lean_object* v___x_610_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v_val_597_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_val_597_);
v___x_610_ = v_reuseFailAlloc_615_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set_tag(v___x_599_, 2);
lean_ctor_set(v___x_599_, 0, v___x_610_);
v___x_612_ = v___x_599_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_614_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_601_, v___x_612_, v_attrKind_569_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_dec_ref_known(v___x_613_, 1);
v_a_581_ = v___x_587_;
goto v___jp_580_;
}
else
{
return v___x_613_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_599_);
lean_dec(v_val_597_);
return v___x_604_;
}
}
}
}
else
{
lean_dec(v_a_596_);
lean_del_object(v___x_593_);
v_a_581_ = v___x_587_;
goto v___jp_580_;
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_del_object(v___x_593_);
v_a_625_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_595_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_595_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
else
{
return v___x_591_;
}
}
v___jp_580_:
{
size_t v___x_582_; size_t v___x_583_; 
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_573_, v___x_582_);
v_i_573_ = v___x_583_;
v_b_574_ = v_a_581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2___boxed(lean_object* v_attrKind_635_, lean_object* v_post_636_, lean_object* v_as_637_, lean_object* v_sz_638_, lean_object* v_i_639_, lean_object* v_b_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
uint8_t v_attrKind_boxed_646_; uint8_t v_post_boxed_647_; size_t v_sz_boxed_648_; size_t v_i_boxed_649_; lean_object* v_res_650_; 
v_attrKind_boxed_646_ = lean_unbox(v_attrKind_635_);
v_post_boxed_647_ = lean_unbox(v_post_636_);
v_sz_boxed_648_ = lean_unbox_usize(v_sz_638_);
lean_dec(v_sz_638_);
v_i_boxed_649_ = lean_unbox_usize(v_i_639_);
lean_dec(v_i_639_);
v_res_650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(v_attrKind_boxed_646_, v_post_boxed_647_, v_as_637_, v_sz_boxed_648_, v_i_boxed_649_, v_b_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v_as_637_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(lean_object* v___y_651_, uint8_t v_isExporting_652_, lean_object* v___x_653_, lean_object* v___y_654_, lean_object* v___x_655_, lean_object* v_a_x3f_656_){
_start:
{
lean_object* v___x_658_; lean_object* v_env_659_; lean_object* v_nextMacroScope_660_; lean_object* v_ngen_661_; lean_object* v_auxDeclNGen_662_; lean_object* v_traceState_663_; lean_object* v_recordedDeps_664_; lean_object* v_messages_665_; lean_object* v_infoState_666_; lean_object* v_snapshotTasks_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_692_; 
v___x_658_ = lean_st_ref_take(v___y_651_);
v_env_659_ = lean_ctor_get(v___x_658_, 0);
v_nextMacroScope_660_ = lean_ctor_get(v___x_658_, 1);
v_ngen_661_ = lean_ctor_get(v___x_658_, 2);
v_auxDeclNGen_662_ = lean_ctor_get(v___x_658_, 3);
v_traceState_663_ = lean_ctor_get(v___x_658_, 4);
v_recordedDeps_664_ = lean_ctor_get(v___x_658_, 6);
v_messages_665_ = lean_ctor_get(v___x_658_, 7);
v_infoState_666_ = lean_ctor_get(v___x_658_, 8);
v_snapshotTasks_667_ = lean_ctor_get(v___x_658_, 9);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v___x_658_, 5);
lean_dec(v_unused_693_);
v___x_669_ = v___x_658_;
v_isShared_670_ = v_isSharedCheck_692_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_snapshotTasks_667_);
lean_inc(v_infoState_666_);
lean_inc(v_messages_665_);
lean_inc(v_recordedDeps_664_);
lean_inc(v_traceState_663_);
lean_inc(v_auxDeclNGen_662_);
lean_inc(v_ngen_661_);
lean_inc(v_nextMacroScope_660_);
lean_inc(v_env_659_);
lean_dec(v___x_658_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_692_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = l_Lean_Environment_setExporting(v_env_659_, v_isExporting_652_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 5, v___x_653_);
lean_ctor_set(v___x_669_, 0, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_nextMacroScope_660_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_ngen_661_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v_auxDeclNGen_662_);
lean_ctor_set(v_reuseFailAlloc_691_, 4, v_traceState_663_);
lean_ctor_set(v_reuseFailAlloc_691_, 5, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_691_, 6, v_recordedDeps_664_);
lean_ctor_set(v_reuseFailAlloc_691_, 7, v_messages_665_);
lean_ctor_set(v_reuseFailAlloc_691_, 8, v_infoState_666_);
lean_ctor_set(v_reuseFailAlloc_691_, 9, v_snapshotTasks_667_);
v___x_673_ = v_reuseFailAlloc_691_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v_mctx_676_; lean_object* v_zetaDeltaFVarIds_677_; lean_object* v_postponed_678_; lean_object* v_diag_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_689_; 
v___x_674_ = lean_st_ref_put(v___y_651_, v___x_673_);
v___x_675_ = lean_st_ref_take(v___y_654_);
v_mctx_676_ = lean_ctor_get(v___x_675_, 0);
v_zetaDeltaFVarIds_677_ = lean_ctor_get(v___x_675_, 2);
v_postponed_678_ = lean_ctor_get(v___x_675_, 3);
v_diag_679_ = lean_ctor_get(v___x_675_, 4);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v___x_675_, 1);
lean_dec(v_unused_690_);
v___x_681_ = v___x_675_;
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_diag_679_);
lean_inc(v_postponed_678_);
lean_inc(v_zetaDeltaFVarIds_677_);
lean_inc(v_mctx_676_);
lean_dec(v___x_675_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_box(0);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_655_);
v___x_685_ = v___x_681_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_mctx_676_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_zetaDeltaFVarIds_677_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_postponed_678_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v_diag_679_);
v___x_685_ = v_reuseFailAlloc_688_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_st_ref_put(v___y_654_, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_683_);
return v___x_687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0___boxed(lean_object* v___y_694_, lean_object* v_isExporting_695_, lean_object* v___x_696_, lean_object* v___y_697_, lean_object* v___x_698_, lean_object* v_a_x3f_699_, lean_object* v___y_700_){
_start:
{
uint8_t v_isExporting_boxed_701_; lean_object* v_res_702_; 
v_isExporting_boxed_701_ = lean_unbox(v_isExporting_695_);
v_res_702_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_694_, v_isExporting_boxed_701_, v___x_696_, v___y_697_, v___x_698_, v_a_x3f_699_);
lean_dec(v_a_x3f_699_);
lean_dec(v___y_697_);
lean_dec(v___y_694_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(lean_object* v_x_703_, uint8_t v_isExporting_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; lean_object* v_env_711_; lean_object* v___x_712_; uint8_t v_isModule_713_; 
v___x_710_ = lean_st_ref_get(v___y_708_);
v_env_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc_ref(v_env_711_);
lean_dec(v___x_710_);
v___x_712_ = l_Lean_Environment_header(v_env_711_);
v_isModule_713_ = lean_ctor_get_uint8(v___x_712_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_712_);
if (v_isModule_713_ == 0)
{
lean_object* v___x_714_; 
lean_dec_ref(v_env_711_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
v___x_714_ = lean_apply_5(v_x_703_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, lean_box(0));
return v___x_714_;
}
else
{
uint8_t v_isExporting_715_; 
v_isExporting_715_ = lean_ctor_get_uint8(v_env_711_, sizeof(void*)*13);
lean_dec_ref(v_env_711_);
if (v_isExporting_704_ == 0)
{
if (v_isExporting_715_ == 0)
{
lean_object* v___x_782_; 
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
v___x_782_ = lean_apply_5(v_x_703_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, lean_box(0));
return v___x_782_;
}
else
{
goto v___jp_716_;
}
}
else
{
if (v_isExporting_715_ == 0)
{
goto v___jp_716_;
}
else
{
lean_object* v___x_783_; 
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
v___x_783_ = lean_apply_5(v_x_703_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, lean_box(0));
return v___x_783_;
}
}
v___jp_716_:
{
lean_object* v___x_717_; lean_object* v_env_718_; lean_object* v_nextMacroScope_719_; lean_object* v_ngen_720_; lean_object* v_auxDeclNGen_721_; lean_object* v_traceState_722_; lean_object* v_recordedDeps_723_; lean_object* v_messages_724_; lean_object* v_infoState_725_; lean_object* v_snapshotTasks_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_780_; 
v___x_717_ = lean_st_ref_take(v___y_708_);
v_env_718_ = lean_ctor_get(v___x_717_, 0);
v_nextMacroScope_719_ = lean_ctor_get(v___x_717_, 1);
v_ngen_720_ = lean_ctor_get(v___x_717_, 2);
v_auxDeclNGen_721_ = lean_ctor_get(v___x_717_, 3);
v_traceState_722_ = lean_ctor_get(v___x_717_, 4);
v_recordedDeps_723_ = lean_ctor_get(v___x_717_, 6);
v_messages_724_ = lean_ctor_get(v___x_717_, 7);
v_infoState_725_ = lean_ctor_get(v___x_717_, 8);
v_snapshotTasks_726_ = lean_ctor_get(v___x_717_, 9);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_717_, 5);
lean_dec(v_unused_781_);
v___x_728_ = v___x_717_;
v_isShared_729_ = v_isSharedCheck_780_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_snapshotTasks_726_);
lean_inc(v_infoState_725_);
lean_inc(v_messages_724_);
lean_inc(v_recordedDeps_723_);
lean_inc(v_traceState_722_);
lean_inc(v_auxDeclNGen_721_);
lean_inc(v_ngen_720_);
lean_inc(v_nextMacroScope_719_);
lean_inc(v_env_718_);
lean_dec(v___x_717_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_780_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_730_ = l_Lean_Environment_setExporting(v_env_718_, v_isExporting_704_);
v___x_731_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 5, v___x_731_);
lean_ctor_set(v___x_728_, 0, v___x_730_);
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_nextMacroScope_719_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_ngen_720_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_auxDeclNGen_721_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_traceState_722_);
lean_ctor_set(v_reuseFailAlloc_779_, 5, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_779_, 6, v_recordedDeps_723_);
lean_ctor_set(v_reuseFailAlloc_779_, 7, v_messages_724_);
lean_ctor_set(v_reuseFailAlloc_779_, 8, v_infoState_725_);
lean_ctor_set(v_reuseFailAlloc_779_, 9, v_snapshotTasks_726_);
v___x_733_ = v_reuseFailAlloc_779_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_mctx_736_; lean_object* v_zetaDeltaFVarIds_737_; lean_object* v_postponed_738_; lean_object* v_diag_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_777_; 
v___x_734_ = lean_st_ref_put(v___y_708_, v___x_733_);
v___x_735_ = lean_st_ref_take(v___y_706_);
v_mctx_736_ = lean_ctor_get(v___x_735_, 0);
v_zetaDeltaFVarIds_737_ = lean_ctor_get(v___x_735_, 2);
v_postponed_738_ = lean_ctor_get(v___x_735_, 3);
v_diag_739_ = lean_ctor_get(v___x_735_, 4);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v___x_735_, 1);
lean_dec(v_unused_778_);
v___x_741_ = v___x_735_;
v_isShared_742_ = v_isSharedCheck_777_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_diag_739_);
lean_inc(v_postponed_738_);
lean_inc(v_zetaDeltaFVarIds_737_);
lean_inc(v_mctx_736_);
lean_dec(v___x_735_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_777_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_mctx_736_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_zetaDeltaFVarIds_737_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_postponed_738_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_diag_739_);
v___x_745_ = v_reuseFailAlloc_776_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_746_; lean_object* v_r_747_; 
v___x_746_ = lean_st_ref_put(v___y_706_, v___x_745_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
v_r_747_ = lean_apply_5(v_x_703_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, lean_box(0));
if (lean_obj_tag(v_r_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_764_; 
v_a_748_ = lean_ctor_get(v_r_747_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_r_747_);
if (v_isSharedCheck_764_ == 0)
{
v___x_750_ = v_r_747_;
v_isShared_751_ = v_isSharedCheck_764_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v_r_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_764_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
lean_inc(v_a_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 1);
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_763_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
v___x_754_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_708_, v_isExporting_715_, v___x_731_, v___y_706_, v___x_743_, v___x_753_);
lean_dec_ref(v___x_753_);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v___x_754_, 0);
lean_dec(v_unused_762_);
v___x_756_ = v___x_754_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_dec(v___x_754_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v_a_748_);
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_748_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
v_a_765_ = lean_ctor_get(v_r_747_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v_r_747_, 1);
v___x_766_ = lean_box(0);
v___x_767_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_708_, v_isExporting_715_, v___x_731_, v___y_706_, v___x_743_, v___x_766_);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v___x_767_, 0);
lean_dec(v_unused_775_);
v___x_769_ = v___x_767_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_dec(v___x_767_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set_tag(v___x_769_, 1);
lean_ctor_set(v___x_769_, 0, v_a_765_);
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_765_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___boxed(lean_object* v_x_784_, lean_object* v_isExporting_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
uint8_t v_isExporting_boxed_791_; lean_object* v_res_792_; 
v_isExporting_boxed_791_ = lean_unbox(v_isExporting_785_);
v_res_792_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_784_, v_isExporting_boxed_791_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem(lean_object* v_declName_793_, uint8_t v_post_794_, uint8_t v_inv_795_, uint8_t v_attrKind_796_, lean_object* v_prio_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___y_809_; uint8_t v___x_832_; uint8_t v___x_833_; 
v___x_803_ = 1;
v___x_804_ = lean_box(v_post_794_);
v___x_805_ = lean_box(v_inv_795_);
v___x_806_ = lean_box(v___x_803_);
lean_inc(v_declName_793_);
v___x_807_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpTheoremFromConst___boxed), 10, 5);
lean_closure_set(v___x_807_, 0, v_declName_793_);
lean_closure_set(v___x_807_, 1, v___x_804_);
lean_closure_set(v___x_807_, 2, v___x_805_);
lean_closure_set(v___x_807_, 3, v_prio_797_);
lean_closure_set(v___x_807_, 4, v___x_806_);
v___x_832_ = 1;
v___x_833_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_796_, v___x_832_);
if (v___x_833_ == 0)
{
uint8_t v___x_834_; 
v___x_834_ = l_Lean_isPrivateName(v_declName_793_);
lean_dec(v_declName_793_);
if (v___x_834_ == 0)
{
v___y_809_ = v___x_803_;
goto v___jp_808_;
}
else
{
v___y_809_ = v___x_833_;
goto v___jp_808_;
}
}
else
{
uint8_t v___x_835_; 
lean_dec(v_declName_793_);
v___x_835_ = 0;
v___y_809_ = v___x_835_;
goto v___jp_808_;
}
v___jp_808_:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v___x_807_, v___y_809_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_812_; size_t v_sz_813_; size_t v___x_814_; lean_object* v___x_815_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v___x_812_ = lean_box(0);
v_sz_813_ = lean_array_size(v_a_811_);
v___x_814_ = ((size_t)0ULL);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(v_attrKind_796_, v_post_794_, v_a_811_, v_sz_813_, v___x_814_, v___x_812_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec(v_a_811_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___x_815_, 0);
lean_dec(v_unused_823_);
v___x_817_ = v___x_815_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_dec(v___x_815_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_812_);
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_812_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
return v___x_815_;
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_824_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_810_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_810_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem___boxed(lean_object* v_declName_836_, lean_object* v_post_837_, lean_object* v_inv_838_, lean_object* v_attrKind_839_, lean_object* v_prio_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
uint8_t v_post_boxed_846_; uint8_t v_inv_boxed_847_; uint8_t v_attrKind_boxed_848_; lean_object* v_res_849_; 
v_post_boxed_846_ = lean_unbox(v_post_837_);
v_inv_boxed_847_ = lean_unbox(v_inv_838_);
v_attrKind_boxed_848_ = lean_unbox(v_attrKind_839_);
v_res_849_ = l_Lean_Meta_Grind_addNormTheorem(v_declName_836_, v_post_boxed_846_, v_inv_boxed_847_, v_attrKind_boxed_848_, v_prio_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(lean_object* v_00_u03b1_850_, lean_object* v_x_851_, uint8_t v_isExporting_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_851_, v_isExporting_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___boxed(lean_object* v_00_u03b1_859_, lean_object* v_x_860_, lean_object* v_isExporting_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
uint8_t v_isExporting_boxed_867_; lean_object* v_res_868_; 
v_isExporting_boxed_867_ = lean_unbox(v_isExporting_861_);
v_res_868_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(v_00_u03b1_859_, v_x_860_, v_isExporting_boxed_867_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(lean_object* v_00_u03b1_869_, lean_object* v_00_u03b2_870_, lean_object* v_00_u03c3_871_, lean_object* v_ext_872_, lean_object* v_b_873_, uint8_t v_kind_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v_ext_872_, v_b_873_, v_kind_874_, v___y_876_, v___y_877_, v___y_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___boxed(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_00_u03c3_883_, lean_object* v_ext_884_, lean_object* v_b_885_, lean_object* v_kind_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v_kind_boxed_892_; lean_object* v_res_893_; 
v_kind_boxed_892_ = lean_unbox(v_kind_886_);
v_res_893_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(v_00_u03b1_881_, v_00_u03b2_882_, v_00_u03c3_883_, v_ext_884_, v_b_885_, v_kind_boxed_892_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg();
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0(lean_object* v_00_u03b2_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(uint8_t v_attrKind_902_, lean_object* v_as_903_, size_t v_sz_904_, size_t v_i_905_, lean_object* v_b_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = lean_usize_dec_lt(v_i_905_, v_sz_904_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v_b_906_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_913_ = lean_box(0);
v_a_914_ = lean_array_uget_borrowed(v_as_903_, v_i_905_);
v___x_915_ = l_Lean_Meta_Grind_normSymExt;
lean_inc(v_a_914_);
v___x_916_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_916_, 0, v_a_914_);
v___x_917_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_915_, v___x_916_, v_attrKind_902_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_917_) == 0)
{
size_t v___x_918_; size_t v___x_919_; 
lean_dec_ref_known(v___x_917_, 1);
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_add(v_i_905_, v___x_918_);
v_i_905_ = v___x_919_;
v_b_906_ = v___x_913_;
goto _start;
}
else
{
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg___boxed(lean_object* v_attrKind_921_, lean_object* v_as_922_, lean_object* v_sz_923_, lean_object* v_i_924_, lean_object* v_b_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
uint8_t v_attrKind_boxed_930_; size_t v_sz_boxed_931_; size_t v_i_boxed_932_; lean_object* v_res_933_; 
v_attrKind_boxed_930_ = lean_unbox(v_attrKind_921_);
v_sz_boxed_931_ = lean_unbox_usize(v_sz_923_);
lean_dec(v_sz_923_);
v_i_boxed_932_ = lean_unbox_usize(v_i_924_);
lean_dec(v_i_924_);
v_res_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_boxed_930_, v_as_922_, v_sz_boxed_931_, v_i_boxed_932_, v_b_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v_as_922_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(lean_object* v_declName_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; lean_object* v_env_938_; uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_937_ = lean_st_ref_get(v___y_935_);
v_env_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc_ref(v_env_938_);
lean_dec(v___x_937_);
v___x_939_ = l_Lean_getReducibilityStatusCore(v_env_938_, v_declName_934_);
v___x_940_ = lean_box(v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg___boxed(lean_object* v_declName_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_942_, v___y_943_);
lean_dec(v___y_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(lean_object* v_declName_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_968_; 
v___x_952_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_946_, v___y_950_);
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_968_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_968_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_968_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
uint8_t v___x_957_; 
v___x_957_ = lean_unbox(v_a_953_);
lean_dec(v_a_953_);
if (v___x_957_ == 0)
{
uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_958_ = 1;
v___x_959_ = lean_box(v___x_958_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_959_);
v___x_961_ = v___x_955_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
else
{
uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_963_ = 0;
v___x_964_ = lean_box(v___x_963_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_964_);
v___x_966_ = v___x_955_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
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
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0___boxed(lean_object* v_declName_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(v_declName_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(uint8_t v_attrKind_976_, lean_object* v_as_977_, size_t v_sz_978_, size_t v_i_979_, lean_object* v_b_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
uint8_t v___x_985_; 
v___x_985_ = lean_usize_dec_lt(v_i_979_, v_sz_978_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v_b_980_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_987_ = lean_box(0);
v_a_988_ = lean_array_uget_borrowed(v_as_977_, v_i_979_);
v___x_989_ = l_Lean_Meta_Grind_normSymExt;
lean_inc(v_a_988_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v_a_988_);
v___x_991_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_989_, v___x_990_, v_attrKind_976_, v___y_981_, v___y_982_, v___y_983_);
if (lean_obj_tag(v___x_991_) == 0)
{
size_t v___x_992_; size_t v___x_993_; 
lean_dec_ref_known(v___x_991_, 1);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_add(v_i_979_, v___x_992_);
v_i_979_ = v___x_993_;
v_b_980_ = v___x_987_;
goto _start;
}
else
{
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg___boxed(lean_object* v_attrKind_995_, lean_object* v_as_996_, lean_object* v_sz_997_, lean_object* v_i_998_, lean_object* v_b_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
uint8_t v_attrKind_boxed_1004_; size_t v_sz_boxed_1005_; size_t v_i_boxed_1006_; lean_object* v_res_1007_; 
v_attrKind_boxed_1004_ = lean_unbox(v_attrKind_995_);
v_sz_boxed_1005_ = lean_unbox_usize(v_sz_997_);
lean_dec(v_sz_997_);
v_i_boxed_1006_ = lean_unbox_usize(v_i_998_);
lean_dec(v_i_998_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_boxed_1004_, v_as_996_, v_sz_boxed_1005_, v_i_boxed_1006_, v_b_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v_as_996_);
return v_res_1007_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold(lean_object* v_declName_1011_, uint8_t v_attrKind_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___x_1021_; 
lean_inc(v_declName_1011_);
v___x_1021_ = l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(v_declName_1011_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1088_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1088_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1088_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___y_1027_; lean_object* v_a_1028_; uint8_t v___x_1047_; 
v___x_1047_ = lean_unbox(v_a_1022_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; 
lean_del_object(v___x_1024_);
lean_inc(v_declName_1011_);
v___x_1048_ = l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(v_declName_1011_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; size_t v_sz_1051_; size_t v___x_1052_; lean_object* v___x_1053_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = lean_box(0);
v_sz_1051_ = lean_array_size(v_a_1049_);
v___x_1052_ = ((size_t)0ULL);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_1012_, v_a_1049_, v_sz_1051_, v___x_1052_, v___x_1050_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1049_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v___x_1054_; 
lean_dec_ref_known(v___x_1053_, 1);
lean_inc(v_declName_1011_);
v___x_1054_ = l_Lean_Meta_Sym_DSimp_Decls_mkEntries(v_declName_1011_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; size_t v_sz_1056_; lean_object* v___x_1057_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v_sz_1056_ = lean_array_size(v_a_1055_);
v___x_1057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_1012_, v_a_1055_, v_sz_1056_, v___x_1052_, v___x_1050_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1055_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_a_1022_);
lean_dec(v_declName_1011_);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v___x_1057_, 0);
lean_dec(v_unused_1065_);
v___x_1059_ = v___x_1057_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_dec(v___x_1057_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1050_);
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1050_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
else
{
lean_object* v_a_1066_; 
v_a_1066_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1066_);
v___y_1027_ = v___x_1057_;
v_a_1028_ = v_a_1066_;
goto v___jp_1026_;
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_a_1067_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1054_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1054_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
lean_inc(v_a_1067_);
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
v___y_1027_ = v___x_1072_;
v_a_1028_ = v_a_1067_;
goto v___jp_1026_;
}
}
}
}
else
{
lean_object* v_a_1075_; 
v_a_1075_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1075_);
v___y_1027_ = v___x_1053_;
v_a_1028_ = v_a_1075_;
goto v___jp_1026_;
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1048_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1048_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
lean_inc(v_a_1076_);
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
v___y_1027_ = v___x_1081_;
v_a_1028_ = v_a_1076_;
goto v___jp_1026_;
}
}
}
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_dec(v_a_1022_);
lean_dec(v_declName_1011_);
v___x_1084_ = lean_box(0);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1084_);
v___x_1086_ = v___x_1024_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
v___jp_1026_:
{
uint8_t v___x_1029_; 
v___x_1029_ = l_Lean_Exception_isInterrupt(v_a_1028_);
if (v___x_1029_ == 0)
{
uint8_t v___x_1030_; 
lean_inc_ref(v_a_1028_);
v___x_1030_ = l_Lean_Exception_isRuntime(v_a_1028_);
if (v___x_1030_ == 0)
{
lean_object* v_toCold_1031_; lean_object* v_options_1032_; uint8_t v_hasTrace_1033_; 
lean_dec_ref(v___y_1027_);
v_toCold_1031_ = lean_ctor_get(v_a_1015_, 0);
v_options_1032_ = lean_ctor_get(v_toCold_1031_, 2);
v_hasTrace_1033_ = lean_ctor_get_uint8(v_options_1032_, sizeof(void*)*1);
if (v_hasTrace_1033_ == 0)
{
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1022_);
lean_dec(v_declName_1011_);
goto v___jp_1018_;
}
else
{
lean_object* v_inheritedTraceOptions_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_inheritedTraceOptions_1034_ = lean_ctor_get(v_toCold_1031_, 11);
v___x_1035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_1036_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_1037_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1034_, v_options_1032_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1022_);
lean_dec(v_declName_1011_);
goto v___jp_1018_;
}
else
{
lean_object* v___x_1038_; uint8_t v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1038_ = lean_obj_once(&l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1, &l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1_once, _init_l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1);
v___x_1039_ = lean_unbox(v_a_1022_);
lean_dec(v_a_1022_);
v___x_1040_ = l_Lean_MessageData_ofConstName(v_declName_1011_, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1038_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = l_Lean_Exception_toMessageData(v_a_1028_);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v___x_1035_, v___x_1045_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
return v___x_1046_;
}
}
}
else
{
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1022_);
lean_dec(v_declName_1011_);
return v___y_1027_;
}
}
else
{
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1022_);
lean_dec(v_declName_1011_);
return v___y_1027_;
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_declName_1011_);
v_a_1089_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1021_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1021_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
v___jp_1018_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___boxed(lean_object* v_declName_1097_, lean_object* v_attrKind_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
uint8_t v_attrKind_boxed_1104_; lean_object* v_res_1105_; 
v_attrKind_boxed_1104_ = lean_unbox(v_attrKind_1098_);
v_res_1105_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v_declName_1097_, v_attrKind_boxed_1104_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(lean_object* v_declName_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_1106_, v___y_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___boxed(lean_object* v_declName_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(v_declName_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(uint8_t v_attrKind_1120_, lean_object* v_as_1121_, size_t v_sz_1122_, size_t v_i_1123_, lean_object* v_b_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_1120_, v_as_1121_, v_sz_1122_, v_i_1123_, v_b_1124_, v___y_1126_, v___y_1127_, v___y_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___boxed(lean_object* v_attrKind_1131_, lean_object* v_as_1132_, lean_object* v_sz_1133_, lean_object* v_i_1134_, lean_object* v_b_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
uint8_t v_attrKind_boxed_1141_; size_t v_sz_boxed_1142_; size_t v_i_boxed_1143_; lean_object* v_res_1144_; 
v_attrKind_boxed_1141_ = lean_unbox(v_attrKind_1131_);
v_sz_boxed_1142_ = lean_unbox_usize(v_sz_1133_);
lean_dec(v_sz_1133_);
v_i_boxed_1143_ = lean_unbox_usize(v_i_1134_);
lean_dec(v_i_1134_);
v_res_1144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(v_attrKind_boxed_1141_, v_as_1132_, v_sz_boxed_1142_, v_i_boxed_1143_, v_b_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec_ref(v_as_1132_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(uint8_t v_attrKind_1145_, lean_object* v_as_1146_, size_t v_sz_1147_, size_t v_i_1148_, lean_object* v_b_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_1145_, v_as_1146_, v_sz_1147_, v_i_1148_, v_b_1149_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___boxed(lean_object* v_attrKind_1156_, lean_object* v_as_1157_, lean_object* v_sz_1158_, lean_object* v_i_1159_, lean_object* v_b_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v_attrKind_boxed_1166_; size_t v_sz_boxed_1167_; size_t v_i_boxed_1168_; lean_object* v_res_1169_; 
v_attrKind_boxed_1166_ = lean_unbox(v_attrKind_1156_);
v_sz_boxed_1167_ = lean_unbox_usize(v_sz_1158_);
lean_dec(v_sz_1158_);
v_i_boxed_1168_ = lean_unbox_usize(v_i_1159_);
lean_dec(v_i_1159_);
v_res_1169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(v_attrKind_boxed_1166_, v_as_1157_, v_sz_boxed_1167_, v_i_boxed_1168_, v_b_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v_as_1157_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold(lean_object* v_declName_1170_, uint8_t v_attrKind_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1177_ = l_Lean_Meta_Grind_normExt;
v___x_1178_ = 0;
v___x_1179_ = lean_unsigned_to_nat(1000u);
lean_inc(v_declName_1170_);
v___x_1180_ = l_Lean_Meta_addDeclToUnfold(v___x_1177_, v_declName_1170_, v___x_1178_, v___x_1178_, v___x_1179_, v_attrKind_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1207_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1207_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1207_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
uint8_t v___x_1185_; 
v___x_1185_ = lean_unbox(v_a_1181_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
lean_dec(v_a_1181_);
lean_dec(v_declName_1170_);
v___x_1186_ = lean_box(v___x_1178_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1186_);
v___x_1188_ = v___x_1183_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
else
{
lean_object* v___x_1190_; 
lean_del_object(v___x_1183_);
v___x_1190_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v_declName_1170_, v_attrKind_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v___x_1190_, 0);
lean_dec(v_unused_1198_);
v___x_1192_ = v___x_1190_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v___x_1190_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v_a_1181_);
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1181_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v_a_1181_);
v_a_1199_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1190_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1190_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_1170_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold___boxed(lean_object* v_declName_1208_, lean_object* v_attrKind_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
uint8_t v_attrKind_boxed_1215_; lean_object* v_res_1216_; 
v_attrKind_boxed_1215_ = lean_unbox(v_attrKind_1209_);
v_res_1216_ = l_Lean_Meta_Grind_addNormDeclToUnfold(v_declName_1208_, v_attrKind_boxed_1215_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(lean_object* v_x_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_obj_tag_nat(v_x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl___boxed(lean_object* v_x_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(v_x_1219_);
lean_dec(v_x_1219_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_1221_, lean_object* v_k_1222_){
_start:
{
switch(lean_obj_tag(v_t_1221_))
{
case 0:
{
lean_object* v_k_1223_; lean_object* v___x_1224_; 
v_k_1223_ = lean_ctor_get(v_t_1221_, 0);
lean_inc(v_k_1223_);
lean_dec_ref_known(v_t_1221_, 1);
v___x_1224_ = lean_apply_1(v_k_1222_, v_k_1223_);
return v___x_1224_;
}
case 1:
{
uint8_t v_eager_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_eager_1225_ = lean_ctor_get_uint8(v_t_1221_, 0);
lean_dec_ref_known(v_t_1221_, 0);
v___x_1226_ = lean_box(v_eager_1225_);
v___x_1227_ = lean_apply_1(v_k_1222_, v___x_1226_);
return v___x_1227_;
}
case 5:
{
lean_object* v_prio_1228_; lean_object* v___x_1229_; 
v_prio_1228_ = lean_ctor_get(v_t_1221_, 0);
lean_inc(v_prio_1228_);
lean_dec_ref_known(v_t_1221_, 1);
v___x_1229_ = lean_apply_1(v_k_1222_, v_prio_1228_);
return v___x_1229_;
}
case 8:
{
uint8_t v_post_1230_; uint8_t v_inv_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_post_1230_ = lean_ctor_get_uint8(v_t_1221_, 0);
v_inv_1231_ = lean_ctor_get_uint8(v_t_1221_, 1);
lean_dec_ref_known(v_t_1221_, 0);
v___x_1232_ = lean_box(v_post_1230_);
v___x_1233_ = lean_box(v_inv_1231_);
v___x_1234_ = lean_apply_2(v_k_1222_, v___x_1232_, v___x_1233_);
return v___x_1234_;
}
case 10:
{
uint8_t v_fallback_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_fallback_1235_ = lean_ctor_get_uint8(v_t_1221_, 0);
lean_dec_ref_known(v_t_1221_, 0);
v___x_1236_ = lean_box(v_fallback_1235_);
v___x_1237_ = lean_apply_1(v_k_1222_, v___x_1236_);
return v___x_1237_;
}
default: 
{
lean_dec(v_t_1221_);
return v_k_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_1238_, lean_object* v_ctorIdx_1239_, lean_object* v_t_1240_, lean_object* v_h_1241_, lean_object* v_k_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1240_, v_k_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_1244_, lean_object* v_ctorIdx_1245_, lean_object* v_t_1246_, lean_object* v_h_1247_, lean_object* v_k_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_1244_, v_ctorIdx_1245_, v_t_1246_, v_h_1247_, v_k_1248_);
lean_dec(v_ctorIdx_1245_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_1250_, lean_object* v_ematch_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1250_, v_ematch_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_1253_, lean_object* v_t_1254_, lean_object* v_h_1255_, lean_object* v_ematch_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1254_, v_ematch_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_1258_, lean_object* v_cases_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1258_, v_cases_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_1261_, lean_object* v_t_1262_, lean_object* v_h_1263_, lean_object* v_cases_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1262_, v_cases_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_1266_, lean_object* v_intro_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1266_, v_intro_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_1269_, lean_object* v_t_1270_, lean_object* v_h_1271_, lean_object* v_intro_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1270_, v_intro_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_1274_, lean_object* v_infer_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1274_, v_infer_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_1277_, lean_object* v_t_1278_, lean_object* v_h_1279_, lean_object* v_infer_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1278_, v_infer_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_1282_, lean_object* v_ext_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1282_, v_ext_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_1285_, lean_object* v_t_1286_, lean_object* v_h_1287_, lean_object* v_ext_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1286_, v_ext_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_1290_, lean_object* v_symbol_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1290_, v_symbol_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_1293_, lean_object* v_t_1294_, lean_object* v_h_1295_, lean_object* v_symbol_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1294_, v_symbol_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_1298_, lean_object* v_inj_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1298_, v_inj_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_1301_, lean_object* v_t_1302_, lean_object* v_h_1303_, lean_object* v_inj_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1302_, v_inj_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_1306_, lean_object* v_funCC_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1306_, v_funCC_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_1309_, lean_object* v_t_1310_, lean_object* v_h_1311_, lean_object* v_funCC_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1310_, v_funCC_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_1314_, lean_object* v_norm_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1314_, v_norm_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_1317_, lean_object* v_t_1318_, lean_object* v_h_1319_, lean_object* v_norm_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1318_, v_norm_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_1322_, lean_object* v_unfold_1323_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1322_, v_unfold_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_1325_, lean_object* v_t_1326_, lean_object* v_h_1327_, lean_object* v_unfold_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1326_, v_unfold_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_1330_, lean_object* v_homo_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1330_, v_homo_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_1333_, lean_object* v_t_1334_, lean_object* v_h_1335_, lean_object* v_homo_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1334_, v_homo_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object* v_t_1338_, lean_object* v_homoPred_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1338_, v_homoPred_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object* v_motive_1341_, lean_object* v_t_1342_, lean_object* v_h_1343_, lean_object* v_homoPred_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1342_, v_homoPred_1344_);
return v___x_1345_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
lean_ctor_set(v___x_1350_, 2, v___x_1349_);
lean_ctor_set(v___x_1350_, 3, v___x_1349_);
lean_ctor_set(v___x_1350_, 4, v___x_1348_);
lean_ctor_set(v___x_1350_, 5, v___x_1348_);
lean_ctor_set(v___x_1350_, 6, v___x_1348_);
lean_ctor_set(v___x_1350_, 7, v___x_1348_);
lean_ctor_set(v___x_1350_, 8, v___x_1348_);
lean_ctor_set(v___x_1350_, 9, v___x_1348_);
lean_ctor_set(v___x_1350_, 10, v___x_1348_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = lean_unsigned_to_nat(32u);
v___x_1352_ = lean_mk_empty_array_with_capacity(v___x_1351_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1354_ = ((size_t)5ULL);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = lean_unsigned_to_nat(32u);
v___x_1357_ = lean_mk_empty_array_with_capacity(v___x_1356_);
v___x_1358_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_1359_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___x_1357_);
lean_ctor_set(v___x_1359_, 2, v___x_1355_);
lean_ctor_set(v___x_1359_, 3, v___x_1355_);
lean_ctor_set_usize(v___x_1359_, 4, v___x_1354_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1360_ = lean_box(1);
v___x_1361_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_1362_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_1363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v___x_1361_);
lean_ctor_set(v___x_1363_, 2, v___x_1360_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; lean_object* v_toCold_1369_; lean_object* v_env_1370_; lean_object* v_options_1371_; uint8_t v___x_1372_; lean_object* v_env_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1368_ = lean_st_ref_get(v___y_1366_);
v_toCold_1369_ = lean_ctor_get(v___y_1365_, 0);
v_env_1370_ = lean_ctor_get(v___x_1368_, 0);
lean_inc_ref(v_env_1370_);
lean_dec(v___x_1368_);
v_options_1371_ = lean_ctor_get(v_toCold_1369_, 2);
v___x_1372_ = 0;
v_env_1373_ = l_Lean_Environment_setRecordingDeps(v_env_1370_, v___x_1372_);
v___x_1374_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_1375_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_1371_);
v___x_1376_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1376_, 0, v_env_1373_);
lean_ctor_set(v___x_1376_, 1, v___x_1374_);
lean_ctor_set(v___x_1376_, 2, v___x_1375_);
lean_ctor_set(v___x_1376_, 3, v_options_1371_);
v___x_1377_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
lean_ctor_set(v___x_1377_, 1, v_msgData_1364_);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_ref_1388_; lean_object* v___x_1389_; lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1398_; 
v_ref_1388_ = lean_ctor_get(v___y_1385_, 2);
v___x_1389_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_1384_, v___y_1385_, v___y_1386_);
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
lean_inc(v_ref_1388_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_ref_1388_);
lean_ctor_set(v___x_1394_, 1, v_a_1390_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set_tag(v___x_1392_, 1);
lean_ctor_set(v___x_1392_, 0, v___x_1394_);
v___x_1396_ = v___x_1392_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_1404_, lean_object* v_msg_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_toCold_1409_; lean_object* v_currRecDepth_1410_; lean_object* v_ref_1411_; uint16_t v_optionFlags_1412_; uint8_t v_suppressElabErrors_1413_; uint8_t v_checkDeprecated_1414_; uint8_t v_isRecordingDeps_1415_; lean_object* v_ref_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_toCold_1409_ = lean_ctor_get(v___y_1406_, 0);
v_currRecDepth_1410_ = lean_ctor_get(v___y_1406_, 1);
v_ref_1411_ = lean_ctor_get(v___y_1406_, 2);
v_optionFlags_1412_ = lean_ctor_get_uint16(v___y_1406_, sizeof(void*)*3);
v_suppressElabErrors_1413_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*3 + 2);
v_checkDeprecated_1414_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1415_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*3 + 4);
v_ref_1416_ = l_Lean_replaceRef(v_ref_1404_, v_ref_1411_);
lean_inc(v_currRecDepth_1410_);
lean_inc_ref(v_toCold_1409_);
v___x_1417_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1417_, 0, v_toCold_1409_);
lean_ctor_set(v___x_1417_, 1, v_currRecDepth_1410_);
lean_ctor_set(v___x_1417_, 2, v_ref_1416_);
lean_ctor_set_uint16(v___x_1417_, sizeof(void*)*3, v_optionFlags_1412_);
lean_ctor_set_uint8(v___x_1417_, sizeof(void*)*3 + 2, v_suppressElabErrors_1413_);
lean_ctor_set_uint8(v___x_1417_, sizeof(void*)*3 + 3, v_checkDeprecated_1414_);
lean_ctor_set_uint8(v___x_1417_, sizeof(void*)*3 + 4, v_isRecordingDeps_1415_);
v___x_1418_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1405_, v___x_1417_, v___y_1407_);
lean_dec_ref_known(v___x_1417_, 3);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_1419_, lean_object* v_msg_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_1419_, v_msg_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v_ref_1419_);
return v_res_1424_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
v___x_1434_ = l_Lean_stringToMessageData(v___x_1433_);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__5));
v___x_1437_ = l_Lean_stringToMessageData(v___x_1436_);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__54(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__53));
v___x_1578_ = l_Lean_stringToMessageData(v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__2));
lean_inc(v_stx_1605_);
v___x_1610_ = l_Lean_Syntax_isOfKind(v_stx_1605_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1611_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1612_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1615_, v_a_1606_, v_a_1607_);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1617_ = lean_unsigned_to_nat(0u);
v___x_1618_ = l_Lean_Syntax_getArg(v_stx_1605_, v___x_1617_);
v___x_1619_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__8));
lean_inc(v___x_1618_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__10));
lean_inc(v___x_1618_);
v___x_1622_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__12));
lean_inc(v___x_1618_);
v___x_1624_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__14));
lean_inc(v___x_1618_);
v___x_1626_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__16));
lean_inc(v___x_1618_);
v___x_1628_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__18));
lean_inc(v___x_1618_);
v___x_1630_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__20));
lean_inc(v___x_1618_);
v___x_1632_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__22));
lean_inc(v___x_1618_);
v___x_1634_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__24));
lean_inc(v___x_1618_);
v___x_1636_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__26));
lean_inc(v___x_1618_);
v___x_1638_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
lean_inc(v___x_1618_);
v___x_1640_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__30));
lean_inc(v___x_1618_);
v___x_1642_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__32));
lean_inc(v___x_1618_);
v___x_1644_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__34));
lean_inc(v___x_1618_);
v___x_1646_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__36));
lean_inc(v___x_1618_);
v___x_1648_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__38));
lean_inc(v___x_1618_);
v___x_1650_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__40));
lean_inc(v___x_1618_);
v___x_1652_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__42));
lean_inc(v___x_1618_);
v___x_1654_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__44));
lean_inc(v___x_1618_);
v___x_1656_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__46));
lean_inc(v___x_1618_);
v___x_1658_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__48));
lean_inc(v___x_1618_);
v___x_1660_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__50));
lean_inc(v___x_1618_);
v___x_1662_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__52));
lean_inc(v___x_1618_);
v___x_1664_ = l_Lean_Syntax_isOfKind(v___x_1618_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec(v___x_1618_);
v___x_1665_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1666_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1669_, v_a_1606_, v_a_1607_);
return v___x_1670_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec(v_stx_1605_);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = l_Lean_Syntax_getArg(v___x_1618_, v___x_1671_);
lean_dec(v___x_1618_);
v___x_1673_ = l_Lean_Syntax_isNatLit_x3f(v___x_1672_);
if (lean_obj_tag(v___x_1673_) == 1)
{
lean_object* v_val_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1682_; 
lean_dec(v___x_1672_);
v_val_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1682_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_val_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1682_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 5);
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_val_1674_);
v___x_1679_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
}
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec(v___x_1673_);
v___x_1683_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__54, &l_Lean_Meta_Grind_getAttrKindCore___closed__54_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__54);
v___x_1684_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_1672_, v___x_1683_, v_a_1606_, v_a_1607_);
lean_dec(v___x_1672_);
return v___x_1684_;
}
}
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1685_ = lean_box(11);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1687_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_1687_, 0, v___x_1610_);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1689_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_1689_, 0, v___x_1656_);
v___x_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
return v___x_1690_;
}
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1691_ = lean_box(9);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
return v___x_1692_;
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = lean_unsigned_to_nat(1u);
v___x_1694_ = l_Lean_Syntax_getArg(v___x_1618_, v___x_1693_);
lean_inc(v___x_1694_);
v___x_1695_ = l_Lean_Syntax_matchesNull(v___x_1694_, v___x_1617_);
if (v___x_1695_ == 0)
{
uint8_t v___x_1696_; 
lean_inc(v___x_1694_);
v___x_1696_ = l_Lean_Syntax_matchesNull(v___x_1694_, v___x_1693_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec(v___x_1694_);
lean_dec(v___x_1618_);
v___x_1697_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1698_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1701_, v_a_1606_, v_a_1607_);
return v___x_1702_;
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1703_ = l_Lean_Syntax_getArg(v___x_1694_, v___x_1617_);
lean_dec(v___x_1694_);
v___x_1704_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
lean_inc(v___x_1703_);
v___x_1705_ = l_Lean_Syntax_isOfKind(v___x_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
v___x_1707_ = l_Lean_Syntax_isOfKind(v___x_1703_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec(v___x_1618_);
v___x_1708_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1709_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1710_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1712_, v_a_1606_, v_a_1607_);
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1714_ = lean_unsigned_to_nat(2u);
v___x_1715_ = l_Lean_Syntax_getArg(v___x_1618_, v___x_1714_);
lean_dec(v___x_1618_);
lean_inc(v___x_1715_);
v___x_1716_ = l_Lean_Syntax_matchesNull(v___x_1715_, v___x_1617_);
if (v___x_1716_ == 0)
{
uint8_t v___x_1717_; 
v___x_1717_ = l_Lean_Syntax_matchesNull(v___x_1715_, v___x_1693_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1718_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1719_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
v___x_1723_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1722_, v_a_1606_, v_a_1607_);
return v___x_1723_;
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_dec(v_stx_1605_);
v___x_1724_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1724_, 0, v___x_1716_);
lean_ctor_set_uint8(v___x_1724_, 1, v___x_1610_);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec(v___x_1715_);
lean_dec(v_stx_1605_);
v___x_1726_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1726_, 0, v___x_1705_);
lean_ctor_set_uint8(v___x_1726_, 1, v___x_1705_);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
return v___x_1727_;
}
}
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
lean_dec(v___x_1703_);
v___x_1728_ = lean_unsigned_to_nat(2u);
v___x_1729_ = l_Lean_Syntax_getArg(v___x_1618_, v___x_1728_);
lean_dec(v___x_1618_);
lean_inc(v___x_1729_);
v___x_1730_ = l_Lean_Syntax_matchesNull(v___x_1729_, v___x_1617_);
if (v___x_1730_ == 0)
{
uint8_t v___x_1731_; 
v___x_1731_ = l_Lean_Syntax_matchesNull(v___x_1729_, v___x_1693_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1732_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1733_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1736_, v_a_1606_, v_a_1607_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v_stx_1605_);
v___x_1738_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1738_, 0, v___x_1610_);
lean_ctor_set_uint8(v___x_1738_, 1, v___x_1610_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec(v___x_1729_);
lean_dec(v_stx_1605_);
v___x_1740_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1740_, 0, v___x_1610_);
lean_ctor_set_uint8(v___x_1740_, 1, v___x_1695_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
}
}
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
lean_dec(v___x_1694_);
v___x_1742_ = lean_unsigned_to_nat(2u);
v___x_1743_ = l_Lean_Syntax_getArg(v___x_1618_, v___x_1742_);
lean_dec(v___x_1618_);
lean_inc(v___x_1743_);
v___x_1744_ = l_Lean_Syntax_matchesNull(v___x_1743_, v___x_1617_);
if (v___x_1744_ == 0)
{
uint8_t v___x_1745_; 
v___x_1745_ = l_Lean_Syntax_matchesNull(v___x_1743_, v___x_1693_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1746_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1747_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1746_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1750_, v_a_1606_, v_a_1607_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec(v_stx_1605_);
v___x_1752_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1752_, 0, v___x_1610_);
lean_ctor_set_uint8(v___x_1752_, 1, v___x_1610_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v___x_1743_);
lean_dec(v_stx_1605_);
v___x_1754_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1754_, 0, v___x_1610_);
lean_ctor_set_uint8(v___x_1754_, 1, v___x_1652_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
}
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1756_ = lean_box(7);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1758_ = lean_box(6);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1760_ = lean_box(4);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1762_ = lean_box(2);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1764_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1764_, 0, v___x_1610_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1766_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1766_, 0, v___x_1640_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1768_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1768_, 0, v___x_1610_);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1771_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__59));
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1773_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
return v___x_1774_;
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1775_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1777_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1779_ = lean_unsigned_to_nat(3u);
v___x_1780_ = l_Lean_Syntax_getArg(v___x_1618_, v___x_1779_);
lean_dec(v___x_1618_);
lean_inc(v___x_1780_);
v___x_1781_ = l_Lean_Syntax_matchesNull(v___x_1780_, v___x_1617_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1780_);
v___x_1783_ = l_Lean_Syntax_matchesNull(v___x_1780_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec(v___x_1780_);
v___x_1784_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1785_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1788_, v_a_1606_, v_a_1607_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1790_ = l_Lean_Syntax_getArg(v___x_1780_, v___x_1617_);
lean_dec(v___x_1780_);
v___x_1791_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1792_ = l_Lean_Syntax_isOfKind(v___x_1790_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1793_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1794_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1793_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1797_, v_a_1606_, v_a_1607_);
return v___x_1798_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v_stx_1605_);
v___x_1799_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1799_, 0, v___x_1610_);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
v___x_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
return v___x_1801_;
}
}
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec(v___x_1780_);
lean_dec(v_stx_1605_);
v___x_1802_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1802_, 0, v___x_1628_);
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
return v___x_1804_;
}
}
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1805_ = lean_unsigned_to_nat(2u);
v___x_1806_ = l_Lean_Syntax_getArg(v___x_1618_, v___x_1805_);
lean_dec(v___x_1618_);
lean_inc(v___x_1806_);
v___x_1807_ = l_Lean_Syntax_matchesNull(v___x_1806_, v___x_1617_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1806_);
v___x_1809_ = l_Lean_Syntax_matchesNull(v___x_1806_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec(v___x_1806_);
v___x_1810_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1811_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1814_, v_a_1606_, v_a_1607_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1816_ = l_Lean_Syntax_getArg(v___x_1806_, v___x_1617_);
lean_dec(v___x_1806_);
v___x_1817_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1818_ = l_Lean_Syntax_isOfKind(v___x_1816_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1819_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1820_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1823_, v_a_1606_, v_a_1607_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec(v_stx_1605_);
v___x_1825_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1825_, 0, v___x_1610_);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec(v___x_1806_);
lean_dec(v_stx_1605_);
v___x_1828_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1828_, 0, v___x_1626_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
}
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1831_ = lean_unsigned_to_nat(1u);
v___x_1832_ = l_Lean_Syntax_getArg(v___x_1618_, v___x_1831_);
lean_dec(v___x_1618_);
lean_inc(v___x_1832_);
v___x_1833_ = l_Lean_Syntax_matchesNull(v___x_1832_, v___x_1617_);
if (v___x_1833_ == 0)
{
uint8_t v___x_1834_; 
lean_inc(v___x_1832_);
v___x_1834_ = l_Lean_Syntax_matchesNull(v___x_1832_, v___x_1831_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec(v___x_1832_);
v___x_1835_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1836_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1839_, v_a_1606_, v_a_1607_);
return v___x_1840_;
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1841_ = l_Lean_Syntax_getArg(v___x_1832_, v___x_1617_);
lean_dec(v___x_1832_);
v___x_1842_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1843_ = l_Lean_Syntax_isOfKind(v___x_1841_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1844_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1845_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1848_, v_a_1606_, v_a_1607_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec(v_stx_1605_);
v___x_1850_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_1850_, 0, v___x_1610_);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_dec(v___x_1832_);
lean_dec(v_stx_1605_);
v___x_1853_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_1853_, 0, v___x_1624_);
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec(v___x_1618_);
lean_dec(v_stx_1605_);
v___x_1856_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1858_ = lean_unsigned_to_nat(1u);
v___x_1859_ = l_Lean_Syntax_getArg(v___x_1618_, v___x_1858_);
lean_dec(v___x_1618_);
lean_inc(v___x_1859_);
v___x_1860_ = l_Lean_Syntax_matchesNull(v___x_1859_, v___x_1617_);
if (v___x_1860_ == 0)
{
uint8_t v___x_1861_; 
lean_inc(v___x_1859_);
v___x_1861_ = l_Lean_Syntax_matchesNull(v___x_1859_, v___x_1858_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec(v___x_1859_);
v___x_1862_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1863_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1866_, v_a_1606_, v_a_1607_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1868_ = l_Lean_Syntax_getArg(v___x_1859_, v___x_1617_);
lean_dec(v___x_1859_);
v___x_1869_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1870_ = l_Lean_Syntax_isOfKind(v___x_1868_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1871_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1872_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1875_, v_a_1606_, v_a_1607_);
return v___x_1876_;
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec(v_stx_1605_);
v___x_1877_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1877_, 0, v___x_1610_);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec(v___x_1859_);
lean_dec(v_stx_1605_);
v___x_1880_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1880_, 0, v___x_1620_);
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
}
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v___x_1883_ = lean_unsigned_to_nat(1u);
v___x_1884_ = l_Lean_Syntax_getArg(v___x_1618_, v___x_1883_);
lean_dec(v___x_1618_);
lean_inc(v___x_1884_);
v___x_1885_ = l_Lean_Syntax_matchesNull(v___x_1884_, v___x_1617_);
if (v___x_1885_ == 0)
{
uint8_t v___x_1886_; 
lean_inc(v___x_1884_);
v___x_1886_ = l_Lean_Syntax_matchesNull(v___x_1884_, v___x_1883_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
lean_dec(v___x_1884_);
v___x_1887_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1888_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1891_, v_a_1606_, v_a_1607_);
return v___x_1892_;
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1893_ = l_Lean_Syntax_getArg(v___x_1884_, v___x_1617_);
lean_dec(v___x_1884_);
v___x_1894_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1895_ = l_Lean_Syntax_isOfKind(v___x_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1896_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1897_ = l_Lean_MessageData_ofSyntax(v_stx_1605_);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1900_, v_a_1606_, v_a_1607_);
return v___x_1901_;
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_dec(v_stx_1605_);
v___x_1902_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1902_, 0, v___x_1610_);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
return v___x_1904_;
}
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_dec(v___x_1884_);
lean_dec(v_stx_1605_);
v___x_1905_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
return v___x_1906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_1907_, v_a_1908_, v_a_1909_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_1912_, lean_object* v_msg_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1913_, v___y_1914_, v___y_1915_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_1918_, lean_object* v_msg_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_1918_, v_msg_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_1924_, lean_object* v_ref_1925_, lean_object* v_msg_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_1925_, v_msg_1926_, v___y_1927_, v___y_1928_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_1931_, lean_object* v_ref_1932_, lean_object* v_msg_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_1931_, v_ref_1932_, v_msg_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v_ref_1932_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1942_ = lean_unsigned_to_nat(1u);
v___x_1943_ = l_Lean_Syntax_getArg(v_stx_1938_, v___x_1942_);
v___x_1944_ = l_Lean_Syntax_isNone(v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = l_Lean_Syntax_getArg(v___x_1943_, v___x_1945_);
lean_dec(v___x_1943_);
v___x_1947_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_1946_, v_a_1939_, v_a_1940_);
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v___x_1943_);
v___x_1948_ = lean_box(3);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
return v___x_1949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_stx_1950_);
return v_res_1954_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_1957_ = l_Lean_stringToMessageData(v___x_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_1962_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1961_, v_a_1958_, v_a_1959_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_1968_, v_a_1969_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_1972_, v_a_1973_, v_a_1974_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_1977_, lean_object* v_b_1978_, uint8_t v_kind_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_toCold_1983_; lean_object* v_currNamespace_1984_; lean_object* v___x_1985_; lean_object* v_env_1986_; lean_object* v_nextMacroScope_1987_; lean_object* v_ngen_1988_; lean_object* v_auxDeclNGen_1989_; lean_object* v_traceState_1990_; lean_object* v_recordedDeps_1991_; lean_object* v_messages_1992_; lean_object* v_infoState_1993_; lean_object* v_snapshotTasks_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2006_; 
v_toCold_1983_ = lean_ctor_get(v___y_1980_, 0);
v_currNamespace_1984_ = lean_ctor_get(v_toCold_1983_, 4);
v___x_1985_ = lean_st_ref_take(v___y_1981_);
v_env_1986_ = lean_ctor_get(v___x_1985_, 0);
v_nextMacroScope_1987_ = lean_ctor_get(v___x_1985_, 1);
v_ngen_1988_ = lean_ctor_get(v___x_1985_, 2);
v_auxDeclNGen_1989_ = lean_ctor_get(v___x_1985_, 3);
v_traceState_1990_ = lean_ctor_get(v___x_1985_, 4);
v_recordedDeps_1991_ = lean_ctor_get(v___x_1985_, 6);
v_messages_1992_ = lean_ctor_get(v___x_1985_, 7);
v_infoState_1993_ = lean_ctor_get(v___x_1985_, 8);
v_snapshotTasks_1994_ = lean_ctor_get(v___x_1985_, 9);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v___x_1985_, 5);
lean_dec(v_unused_2007_);
v___x_1996_ = v___x_1985_;
v_isShared_1997_ = v_isSharedCheck_2006_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_snapshotTasks_1994_);
lean_inc(v_infoState_1993_);
lean_inc(v_messages_1992_);
lean_inc(v_recordedDeps_1991_);
lean_inc(v_traceState_1990_);
lean_inc(v_auxDeclNGen_1989_);
lean_inc(v_ngen_1988_);
lean_inc(v_nextMacroScope_1987_);
lean_inc(v_env_1986_);
lean_dec(v___x_1985_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2006_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_1998_ = lean_box(0);
lean_inc(v_currNamespace_1984_);
v___x_1999_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1986_, v_ext_1977_, v_b_1978_, v_kind_1979_, v_currNamespace_1984_);
v___x_2000_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 5, v___x_2000_);
lean_ctor_set(v___x_1996_, 0, v___x_1999_);
v___x_2002_ = v___x_1996_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_nextMacroScope_1987_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_ngen_1988_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v_auxDeclNGen_1989_);
lean_ctor_set(v_reuseFailAlloc_2005_, 4, v_traceState_1990_);
lean_ctor_set(v_reuseFailAlloc_2005_, 5, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2005_, 6, v_recordedDeps_1991_);
lean_ctor_set(v_reuseFailAlloc_2005_, 7, v_messages_1992_);
lean_ctor_set(v_reuseFailAlloc_2005_, 8, v_infoState_1993_);
lean_ctor_set(v_reuseFailAlloc_2005_, 9, v_snapshotTasks_1994_);
v___x_2002_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_st_ref_put(v___y_1981_, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_1998_);
return v___x_2004_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_2008_, lean_object* v_b_2009_, lean_object* v_kind_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
uint8_t v_kind_boxed_2014_; lean_object* v_res_2015_; 
v_kind_boxed_2014_ = lean_unbox(v_kind_2010_);
v_res_2015_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2008_, v_b_2009_, v_kind_boxed_2014_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_2016_, lean_object* v_00_u03b2_2017_, lean_object* v_00_u03c3_2018_, lean_object* v_ext_2019_, lean_object* v_b_2020_, uint8_t v_kind_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2019_, v_b_2020_, v_kind_2021_, v___y_2022_, v___y_2023_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_2026_, lean_object* v_00_u03b2_2027_, lean_object* v_00_u03c3_2028_, lean_object* v_ext_2029_, lean_object* v_b_2030_, lean_object* v_kind_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v_kind_boxed_2035_; lean_object* v_res_2036_; 
v_kind_boxed_2035_ = lean_unbox(v_kind_2031_);
v_res_2036_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_2026_, v_00_u03b2_2027_, v_00_u03c3_2028_, v_ext_2029_, v_b_2030_, v_kind_boxed_2035_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_2037_, lean_object* v_declName_2038_, uint8_t v_eager_2039_, uint8_t v_attrKind_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v___x_2044_; 
lean_inc(v_declName_2038_);
v___x_2044_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_2038_, v_eager_2039_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_dec_ref_known(v___x_2044_, 1);
v___x_2045_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2045_, 0, v_declName_2038_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*1, v_eager_2039_);
v___x_2046_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2037_, v___x_2045_, v_attrKind_2040_, v_a_2041_, v_a_2042_);
return v___x_2046_;
}
else
{
lean_dec(v_declName_2038_);
lean_dec_ref(v_ext_2037_);
return v___x_2044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_2047_, lean_object* v_declName_2048_, lean_object* v_eager_2049_, lean_object* v_attrKind_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
uint8_t v_eager_boxed_2054_; uint8_t v_attrKind_boxed_2055_; lean_object* v_res_2056_; 
v_eager_boxed_2054_ = lean_unbox(v_eager_2049_);
v_attrKind_boxed_2055_ = lean_unbox(v_attrKind_2050_);
v_res_2056_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2047_, v_declName_2048_, v_eager_boxed_2054_, v_attrKind_boxed_2055_, v_a_2051_, v_a_2052_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_2057_, lean_object* v_declName_2058_, uint8_t v_attrKind_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v___x_2063_; 
lean_inc(v_declName_2058_);
v___x_2063_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_2058_, v_a_2060_, v_a_2061_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v___x_2063_, 0);
lean_dec(v_unused_2072_);
v___x_2065_ = v___x_2063_;
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
else
{
lean_dec(v___x_2063_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v_declName_2058_);
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_declName_2058_);
v___x_2068_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2057_, v___x_2068_, v_attrKind_2059_, v_a_2060_, v_a_2061_);
return v___x_2069_;
}
}
}
else
{
lean_dec(v_declName_2058_);
lean_dec_ref(v_ext_2057_);
return v___x_2063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_2073_, lean_object* v_declName_2074_, lean_object* v_attrKind_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
uint8_t v_attrKind_boxed_2079_; lean_object* v_res_2080_; 
v_attrKind_boxed_2079_ = lean_unbox(v_attrKind_2075_);
v_res_2080_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2073_, v_declName_2074_, v_attrKind_boxed_2079_, v_a_2076_, v_a_2077_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_2081_, lean_object* v_declName_2082_, uint8_t v_attrKind_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_declName_2082_);
v___x_2088_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2081_, v___x_2087_, v_attrKind_2083_, v_a_2084_, v_a_2085_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_2089_, lean_object* v_declName_2090_, lean_object* v_attrKind_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
uint8_t v_attrKind_boxed_2095_; lean_object* v_res_2096_; 
v_attrKind_boxed_2095_ = lean_unbox(v_attrKind_2091_);
v_res_2096_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2089_, v_declName_2090_, v_attrKind_boxed_2095_, v_a_2092_, v_a_2093_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_2097_, lean_object* v_s_2098_){
_start:
{
lean_object* v_casesTypes_2099_; lean_object* v_funCC_2100_; lean_object* v_ematch_2101_; lean_object* v_inj_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
v_casesTypes_2099_ = lean_ctor_get(v_s_2098_, 0);
v_funCC_2100_ = lean_ctor_get(v_s_2098_, 2);
v_ematch_2101_ = lean_ctor_get(v_s_2098_, 3);
v_inj_2102_ = lean_ctor_get(v_s_2098_, 4);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_s_2098_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; 
v_unused_2110_ = lean_ctor_get(v_s_2098_, 1);
lean_dec(v_unused_2110_);
v___x_2104_ = v_s_2098_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_inj_2102_);
lean_inc(v_ematch_2101_);
lean_inc(v_funCC_2100_);
lean_inc(v_casesTypes_2099_);
lean_dec(v_s_2098_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 1, v_a_2097_);
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_casesTypes_2099_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_a_2097_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_funCC_2100_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_ematch_2101_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v_inj_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_2111_, lean_object* v_declName_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v_ext_2118_; lean_object* v_toEnvExtension_2119_; lean_object* v_env_2120_; lean_object* v_asyncMode_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v_extThms_2124_; lean_object* v___x_2125_; 
v___x_2116_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2117_ = lean_st_ref_get(v_a_2114_);
v_ext_2118_ = lean_ctor_get(v_ext_2111_, 1);
v_toEnvExtension_2119_ = lean_ctor_get(v_ext_2118_, 0);
v_env_2120_ = lean_ctor_get(v___x_2117_, 0);
lean_inc_ref(v_env_2120_);
lean_dec(v___x_2117_);
v_asyncMode_2121_ = lean_ctor_get(v_toEnvExtension_2119_, 2);
v___x_2122_ = 0;
v___x_2123_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2116_, v_ext_2111_, v_env_2120_, v_asyncMode_2121_, v___x_2122_);
v_extThms_2124_ = lean_ctor_get(v___x_2123_, 1);
lean_inc_ref(v_extThms_2124_);
lean_dec(v___x_2123_);
v___x_2125_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_2124_, v_declName_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2156_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2156_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2156_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___f_2130_; lean_object* v___x_2131_; lean_object* v_env_2132_; lean_object* v_nextMacroScope_2133_; lean_object* v_ngen_2134_; lean_object* v_auxDeclNGen_2135_; lean_object* v_traceState_2136_; lean_object* v_recordedDeps_2137_; lean_object* v_messages_2138_; lean_object* v_infoState_2139_; lean_object* v_snapshotTasks_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2154_; 
v___f_2130_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_2130_, 0, v_a_2126_);
v___x_2131_ = lean_st_ref_take(v_a_2114_);
v_env_2132_ = lean_ctor_get(v___x_2131_, 0);
v_nextMacroScope_2133_ = lean_ctor_get(v___x_2131_, 1);
v_ngen_2134_ = lean_ctor_get(v___x_2131_, 2);
v_auxDeclNGen_2135_ = lean_ctor_get(v___x_2131_, 3);
v_traceState_2136_ = lean_ctor_get(v___x_2131_, 4);
v_recordedDeps_2137_ = lean_ctor_get(v___x_2131_, 6);
v_messages_2138_ = lean_ctor_get(v___x_2131_, 7);
v_infoState_2139_ = lean_ctor_get(v___x_2131_, 8);
v_snapshotTasks_2140_ = lean_ctor_get(v___x_2131_, 9);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v___x_2131_, 5);
lean_dec(v_unused_2155_);
v___x_2142_ = v___x_2131_;
v_isShared_2143_ = v_isSharedCheck_2154_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_snapshotTasks_2140_);
lean_inc(v_infoState_2139_);
lean_inc(v_messages_2138_);
lean_inc(v_recordedDeps_2137_);
lean_inc(v_traceState_2136_);
lean_inc(v_auxDeclNGen_2135_);
lean_inc(v_ngen_2134_);
lean_inc(v_nextMacroScope_2133_);
lean_inc(v_env_2132_);
lean_dec(v___x_2131_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2154_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2144_ = lean_box(0);
v___x_2145_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2111_, v_env_2132_, v___f_2130_);
v___x_2146_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 5, v___x_2146_);
lean_ctor_set(v___x_2142_, 0, v___x_2145_);
v___x_2148_ = v___x_2142_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_nextMacroScope_2133_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_ngen_2134_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_auxDeclNGen_2135_);
lean_ctor_set(v_reuseFailAlloc_2153_, 4, v_traceState_2136_);
lean_ctor_set(v_reuseFailAlloc_2153_, 5, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2153_, 6, v_recordedDeps_2137_);
lean_ctor_set(v_reuseFailAlloc_2153_, 7, v_messages_2138_);
lean_ctor_set(v_reuseFailAlloc_2153_, 8, v_infoState_2139_);
lean_ctor_set(v_reuseFailAlloc_2153_, 9, v_snapshotTasks_2140_);
v___x_2148_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = lean_st_ref_put(v_a_2114_, v___x_2148_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2144_);
v___x_2151_ = v___x_2128_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2144_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec_ref(v_ext_2111_);
v_a_2157_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2125_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2125_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_2165_, lean_object* v_declName_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2165_, v_declName_2166_, v_a_2167_, v_a_2168_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_2171_, lean_object* v_s_2172_){
_start:
{
lean_object* v_extThms_2173_; lean_object* v_funCC_2174_; lean_object* v_ematch_2175_; lean_object* v_inj_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
v_extThms_2173_ = lean_ctor_get(v_s_2172_, 1);
v_funCC_2174_ = lean_ctor_get(v_s_2172_, 2);
v_ematch_2175_ = lean_ctor_get(v_s_2172_, 3);
v_inj_2176_ = lean_ctor_get(v_s_2172_, 4);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_s_2172_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; 
v_unused_2184_ = lean_ctor_get(v_s_2172_, 0);
lean_dec(v_unused_2184_);
v___x_2178_ = v_s_2172_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_inj_2176_);
lean_inc(v_ematch_2175_);
lean_inc(v_funCC_2174_);
lean_inc(v_extThms_2173_);
lean_dec(v_s_2172_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v_a_2171_);
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2171_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_extThms_2173_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_funCC_2174_);
lean_ctor_set(v_reuseFailAlloc_2182_, 3, v_ematch_2175_);
lean_ctor_set(v_reuseFailAlloc_2182_, 4, v_inj_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_2185_, lean_object* v_declName_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_inc(v_declName_2186_);
v___x_2191_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v___x_2192_; lean_object* v_ext_2193_; lean_object* v_toEnvExtension_2194_; lean_object* v_env_2195_; lean_object* v_asyncMode_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v_casesTypes_2199_; lean_object* v___x_2200_; 
lean_dec_ref_known(v___x_2191_, 1);
v___x_2192_ = lean_st_ref_get(v_a_2188_);
v_ext_2193_ = lean_ctor_get(v_ext_2185_, 1);
v_toEnvExtension_2194_ = lean_ctor_get(v_ext_2193_, 0);
v_env_2195_ = lean_ctor_get(v___x_2192_, 0);
lean_inc_ref(v_env_2195_);
lean_dec(v___x_2192_);
v_asyncMode_2196_ = lean_ctor_get(v_toEnvExtension_2194_, 2);
v___x_2197_ = 0;
v___x_2198_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2190_, v_ext_2185_, v_env_2195_, v_asyncMode_2196_, v___x_2197_);
v_casesTypes_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc_ref(v_casesTypes_2199_);
lean_dec(v___x_2198_);
v___x_2200_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_2199_, v_declName_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2231_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2231_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2231_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___f_2205_; lean_object* v___x_2206_; lean_object* v_env_2207_; lean_object* v_nextMacroScope_2208_; lean_object* v_ngen_2209_; lean_object* v_auxDeclNGen_2210_; lean_object* v_traceState_2211_; lean_object* v_recordedDeps_2212_; lean_object* v_messages_2213_; lean_object* v_infoState_2214_; lean_object* v_snapshotTasks_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2229_; 
v___f_2205_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_2205_, 0, v_a_2201_);
v___x_2206_ = lean_st_ref_take(v_a_2188_);
v_env_2207_ = lean_ctor_get(v___x_2206_, 0);
v_nextMacroScope_2208_ = lean_ctor_get(v___x_2206_, 1);
v_ngen_2209_ = lean_ctor_get(v___x_2206_, 2);
v_auxDeclNGen_2210_ = lean_ctor_get(v___x_2206_, 3);
v_traceState_2211_ = lean_ctor_get(v___x_2206_, 4);
v_recordedDeps_2212_ = lean_ctor_get(v___x_2206_, 6);
v_messages_2213_ = lean_ctor_get(v___x_2206_, 7);
v_infoState_2214_ = lean_ctor_get(v___x_2206_, 8);
v_snapshotTasks_2215_ = lean_ctor_get(v___x_2206_, 9);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; 
v_unused_2230_ = lean_ctor_get(v___x_2206_, 5);
lean_dec(v_unused_2230_);
v___x_2217_ = v___x_2206_;
v_isShared_2218_ = v_isSharedCheck_2229_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_snapshotTasks_2215_);
lean_inc(v_infoState_2214_);
lean_inc(v_messages_2213_);
lean_inc(v_recordedDeps_2212_);
lean_inc(v_traceState_2211_);
lean_inc(v_auxDeclNGen_2210_);
lean_inc(v_ngen_2209_);
lean_inc(v_nextMacroScope_2208_);
lean_inc(v_env_2207_);
lean_dec(v___x_2206_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2229_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2219_ = lean_box(0);
v___x_2220_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2185_, v_env_2207_, v___f_2205_);
v___x_2221_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 5, v___x_2221_);
lean_ctor_set(v___x_2217_, 0, v___x_2220_);
v___x_2223_ = v___x_2217_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_nextMacroScope_2208_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_ngen_2209_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_auxDeclNGen_2210_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_traceState_2211_);
lean_ctor_set(v_reuseFailAlloc_2228_, 5, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2228_, 6, v_recordedDeps_2212_);
lean_ctor_set(v_reuseFailAlloc_2228_, 7, v_messages_2213_);
lean_ctor_set(v_reuseFailAlloc_2228_, 8, v_infoState_2214_);
lean_ctor_set(v_reuseFailAlloc_2228_, 9, v_snapshotTasks_2215_);
v___x_2223_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_st_ref_put(v_a_2188_, v___x_2223_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2219_);
v___x_2226_ = v___x_2203_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2219_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_ext_2185_);
v_a_2232_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2200_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2200_);
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
else
{
lean_dec(v_declName_2186_);
lean_dec_ref(v_ext_2185_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_2240_, lean_object* v_declName_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2240_, v_declName_2241_, v_a_2242_, v_a_2243_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_2246_, lean_object* v_s_2247_){
_start:
{
lean_object* v_casesTypes_2248_; lean_object* v_extThms_2249_; lean_object* v_ematch_2250_; lean_object* v_inj_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
v_casesTypes_2248_ = lean_ctor_get(v_s_2247_, 0);
v_extThms_2249_ = lean_ctor_get(v_s_2247_, 1);
v_ematch_2250_ = lean_ctor_get(v_s_2247_, 3);
v_inj_2251_ = lean_ctor_get(v_s_2247_, 4);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_s_2247_);
if (v_isSharedCheck_2258_ == 0)
{
lean_object* v_unused_2259_; 
v_unused_2259_ = lean_ctor_get(v_s_2247_, 2);
lean_dec(v_unused_2259_);
v___x_2253_ = v_s_2247_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_inj_2251_);
lean_inc(v_ematch_2250_);
lean_inc(v_extThms_2249_);
lean_inc(v_casesTypes_2248_);
lean_dec(v_s_2247_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 2, v___x_2246_);
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_casesTypes_2248_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_extThms_2249_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_ematch_2250_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v_inj_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_2260_, lean_object* v_t_2261_){
_start:
{
if (lean_obj_tag(v_t_2261_) == 0)
{
lean_object* v_k_2262_; lean_object* v_v_2263_; lean_object* v_l_2264_; lean_object* v_r_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2919_; 
v_k_2262_ = lean_ctor_get(v_t_2261_, 1);
v_v_2263_ = lean_ctor_get(v_t_2261_, 2);
v_l_2264_ = lean_ctor_get(v_t_2261_, 3);
v_r_2265_ = lean_ctor_get(v_t_2261_, 4);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_t_2261_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v_t_2261_, 0);
lean_dec(v_unused_2920_);
v___x_2267_ = v_t_2261_;
v_isShared_2268_ = v_isSharedCheck_2919_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_r_2265_);
lean_inc(v_l_2264_);
lean_inc(v_v_2263_);
lean_inc(v_k_2262_);
lean_dec(v_t_2261_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2919_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
uint8_t v___x_2269_; 
v___x_2269_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2260_, v_k_2262_);
switch(v___x_2269_)
{
case 0:
{
lean_object* v_impl_2270_; lean_object* v___x_2271_; 
v_impl_2270_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2260_, v_l_2264_);
v___x_2271_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2270_) == 0)
{
if (lean_obj_tag(v_r_2265_) == 0)
{
lean_object* v_size_2272_; lean_object* v_size_2273_; lean_object* v_k_2274_; lean_object* v_v_2275_; lean_object* v_l_2276_; lean_object* v_r_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v_size_2272_ = lean_ctor_get(v_impl_2270_, 0);
v_size_2273_ = lean_ctor_get(v_r_2265_, 0);
v_k_2274_ = lean_ctor_get(v_r_2265_, 1);
v_v_2275_ = lean_ctor_get(v_r_2265_, 2);
v_l_2276_ = lean_ctor_get(v_r_2265_, 3);
lean_inc(v_l_2276_);
v_r_2277_ = lean_ctor_get(v_r_2265_, 4);
v___x_2278_ = lean_unsigned_to_nat(3u);
v___x_2279_ = lean_nat_mul(v___x_2278_, v_size_2272_);
v___x_2280_ = lean_nat_dec_lt(v___x_2279_, v_size_2273_);
lean_dec(v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
lean_dec(v_l_2276_);
v___x_2281_ = lean_nat_add(v___x_2271_, v_size_2272_);
v___x_2282_ = lean_nat_add(v___x_2281_, v_size_2273_);
lean_dec(v___x_2281_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 3, v_impl_2270_);
lean_ctor_set(v___x_2267_, 0, v___x_2282_);
v___x_2284_ = v___x_2267_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2285_, 3, v_impl_2270_);
lean_ctor_set(v_reuseFailAlloc_2285_, 4, v_r_2265_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
else
{
lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2349_; 
lean_inc(v_r_2277_);
lean_inc(v_v_2275_);
lean_inc(v_k_2274_);
lean_inc(v_size_2273_);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_r_2265_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; lean_object* v_unused_2351_; lean_object* v_unused_2352_; lean_object* v_unused_2353_; lean_object* v_unused_2354_; 
v_unused_2350_ = lean_ctor_get(v_r_2265_, 4);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_r_2265_, 3);
lean_dec(v_unused_2351_);
v_unused_2352_ = lean_ctor_get(v_r_2265_, 2);
lean_dec(v_unused_2352_);
v_unused_2353_ = lean_ctor_get(v_r_2265_, 1);
lean_dec(v_unused_2353_);
v_unused_2354_ = lean_ctor_get(v_r_2265_, 0);
lean_dec(v_unused_2354_);
v___x_2287_ = v_r_2265_;
v_isShared_2288_ = v_isSharedCheck_2349_;
goto v_resetjp_2286_;
}
else
{
lean_dec(v_r_2265_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2349_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v_size_2289_; lean_object* v_k_2290_; lean_object* v_v_2291_; lean_object* v_l_2292_; lean_object* v_r_2293_; lean_object* v_size_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v_size_2289_ = lean_ctor_get(v_l_2276_, 0);
v_k_2290_ = lean_ctor_get(v_l_2276_, 1);
v_v_2291_ = lean_ctor_get(v_l_2276_, 2);
v_l_2292_ = lean_ctor_get(v_l_2276_, 3);
v_r_2293_ = lean_ctor_get(v_l_2276_, 4);
v_size_2294_ = lean_ctor_get(v_r_2277_, 0);
v___x_2295_ = lean_unsigned_to_nat(2u);
v___x_2296_ = lean_nat_mul(v___x_2295_, v_size_2294_);
v___x_2297_ = lean_nat_dec_lt(v_size_2289_, v___x_2296_);
lean_dec(v___x_2296_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2325_; 
lean_inc(v_r_2293_);
lean_inc(v_l_2292_);
lean_inc(v_v_2291_);
lean_inc(v_k_2290_);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_l_2276_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; lean_object* v_unused_2327_; lean_object* v_unused_2328_; lean_object* v_unused_2329_; lean_object* v_unused_2330_; 
v_unused_2326_ = lean_ctor_get(v_l_2276_, 4);
lean_dec(v_unused_2326_);
v_unused_2327_ = lean_ctor_get(v_l_2276_, 3);
lean_dec(v_unused_2327_);
v_unused_2328_ = lean_ctor_get(v_l_2276_, 2);
lean_dec(v_unused_2328_);
v_unused_2329_ = lean_ctor_get(v_l_2276_, 1);
lean_dec(v_unused_2329_);
v_unused_2330_ = lean_ctor_get(v_l_2276_, 0);
lean_dec(v_unused_2330_);
v___x_2299_ = v_l_2276_;
v_isShared_2300_ = v_isSharedCheck_2325_;
goto v_resetjp_2298_;
}
else
{
lean_dec(v_l_2276_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2325_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2315_; 
v___x_2301_ = lean_nat_add(v___x_2271_, v_size_2272_);
v___x_2302_ = lean_nat_add(v___x_2301_, v_size_2273_);
lean_dec(v_size_2273_);
if (lean_obj_tag(v_l_2292_) == 0)
{
lean_object* v_size_2323_; 
v_size_2323_ = lean_ctor_get(v_l_2292_, 0);
lean_inc(v_size_2323_);
v___y_2315_ = v_size_2323_;
goto v___jp_2314_;
}
else
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_unsigned_to_nat(0u);
v___y_2315_ = v___x_2324_;
goto v___jp_2314_;
}
v___jp_2303_:
{
lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2307_ = lean_nat_add(v___y_2304_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec(v___y_2304_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 4, v_r_2277_);
lean_ctor_set(v___x_2299_, 3, v_r_2293_);
lean_ctor_set(v___x_2299_, 2, v_v_2275_);
lean_ctor_set(v___x_2299_, 1, v_k_2274_);
lean_ctor_set(v___x_2299_, 0, v___x_2307_);
v___x_2309_ = v___x_2299_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_k_2274_);
lean_ctor_set(v_reuseFailAlloc_2313_, 2, v_v_2275_);
lean_ctor_set(v_reuseFailAlloc_2313_, 3, v_r_2293_);
lean_ctor_set(v_reuseFailAlloc_2313_, 4, v_r_2277_);
v___x_2309_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2311_; 
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 4, v___x_2309_);
lean_ctor_set(v___x_2287_, 3, v___y_2305_);
lean_ctor_set(v___x_2287_, 2, v_v_2291_);
lean_ctor_set(v___x_2287_, 1, v_k_2290_);
lean_ctor_set(v___x_2287_, 0, v___x_2302_);
v___x_2311_ = v___x_2287_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v___y_2305_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
v___jp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2316_ = lean_nat_add(v___x_2301_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec(v___x_2301_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_l_2292_);
lean_ctor_set(v___x_2267_, 3, v_impl_2270_);
lean_ctor_set(v___x_2267_, 0, v___x_2316_);
v___x_2318_ = v___x_2267_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2322_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_impl_2270_);
lean_ctor_set(v_reuseFailAlloc_2322_, 4, v_l_2292_);
v___x_2318_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_nat_add(v___x_2271_, v_size_2294_);
if (lean_obj_tag(v_r_2293_) == 0)
{
lean_object* v_size_2320_; 
v_size_2320_ = lean_ctor_get(v_r_2293_, 0);
lean_inc(v_size_2320_);
v___y_2304_ = v___x_2319_;
v___y_2305_ = v___x_2318_;
v___y_2306_ = v_size_2320_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_unsigned_to_nat(0u);
v___y_2304_ = v___x_2319_;
v___y_2305_ = v___x_2318_;
v___y_2306_ = v___x_2321_;
goto v___jp_2303_;
}
}
}
}
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
lean_del_object(v___x_2267_);
v___x_2331_ = lean_nat_add(v___x_2271_, v_size_2272_);
v___x_2332_ = lean_nat_add(v___x_2331_, v_size_2273_);
lean_dec(v_size_2273_);
v___x_2333_ = lean_nat_add(v___x_2331_, v_size_2289_);
lean_dec(v___x_2331_);
lean_inc_ref(v_impl_2270_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 4, v_l_2276_);
lean_ctor_set(v___x_2287_, 3, v_impl_2270_);
lean_ctor_set(v___x_2287_, 2, v_v_2263_);
lean_ctor_set(v___x_2287_, 1, v_k_2262_);
lean_ctor_set(v___x_2287_, 0, v___x_2333_);
v___x_2335_ = v___x_2287_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_impl_2270_);
lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_l_2276_);
v___x_2335_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
v_isSharedCheck_2342_ = !lean_is_exclusive(v_impl_2270_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; lean_object* v_unused_2344_; lean_object* v_unused_2345_; lean_object* v_unused_2346_; lean_object* v_unused_2347_; 
v_unused_2343_ = lean_ctor_get(v_impl_2270_, 4);
lean_dec(v_unused_2343_);
v_unused_2344_ = lean_ctor_get(v_impl_2270_, 3);
lean_dec(v_unused_2344_);
v_unused_2345_ = lean_ctor_get(v_impl_2270_, 2);
lean_dec(v_unused_2345_);
v_unused_2346_ = lean_ctor_get(v_impl_2270_, 1);
lean_dec(v_unused_2346_);
v_unused_2347_ = lean_ctor_get(v_impl_2270_, 0);
lean_dec(v_unused_2347_);
v___x_2337_ = v_impl_2270_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_dec(v_impl_2270_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 4, v_r_2277_);
lean_ctor_set(v___x_2337_, 3, v___x_2335_);
lean_ctor_set(v___x_2337_, 2, v_v_2275_);
lean_ctor_set(v___x_2337_, 1, v_k_2274_);
lean_ctor_set(v___x_2337_, 0, v___x_2332_);
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_k_2274_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_v_2275_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v_r_2277_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
v_size_2355_ = lean_ctor_get(v_impl_2270_, 0);
v___x_2356_ = lean_nat_add(v___x_2271_, v_size_2355_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 3, v_impl_2270_);
lean_ctor_set(v___x_2267_, 0, v___x_2356_);
v___x_2358_ = v___x_2267_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_impl_2270_);
lean_ctor_set(v_reuseFailAlloc_2359_, 4, v_r_2265_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
else
{
if (lean_obj_tag(v_r_2265_) == 0)
{
lean_object* v_l_2360_; 
v_l_2360_ = lean_ctor_get(v_r_2265_, 3);
lean_inc(v_l_2360_);
if (lean_obj_tag(v_l_2360_) == 0)
{
lean_object* v_r_2361_; 
v_r_2361_ = lean_ctor_get(v_r_2265_, 4);
lean_inc(v_r_2361_);
if (lean_obj_tag(v_r_2361_) == 0)
{
lean_object* v_size_2362_; lean_object* v_k_2363_; lean_object* v_v_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2377_; 
v_size_2362_ = lean_ctor_get(v_r_2265_, 0);
v_k_2363_ = lean_ctor_get(v_r_2265_, 1);
v_v_2364_ = lean_ctor_get(v_r_2265_, 2);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_r_2265_);
if (v_isSharedCheck_2377_ == 0)
{
lean_object* v_unused_2378_; lean_object* v_unused_2379_; 
v_unused_2378_ = lean_ctor_get(v_r_2265_, 4);
lean_dec(v_unused_2378_);
v_unused_2379_ = lean_ctor_get(v_r_2265_, 3);
lean_dec(v_unused_2379_);
v___x_2366_ = v_r_2265_;
v_isShared_2367_ = v_isSharedCheck_2377_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_v_2364_);
lean_inc(v_k_2363_);
lean_inc(v_size_2362_);
lean_dec(v_r_2265_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2377_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_size_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; 
v_size_2368_ = lean_ctor_get(v_l_2360_, 0);
v___x_2369_ = lean_nat_add(v___x_2271_, v_size_2362_);
lean_dec(v_size_2362_);
v___x_2370_ = lean_nat_add(v___x_2271_, v_size_2368_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 4, v_l_2360_);
lean_ctor_set(v___x_2366_, 3, v_impl_2270_);
lean_ctor_set(v___x_2366_, 2, v_v_2263_);
lean_ctor_set(v___x_2366_, 1, v_k_2262_);
lean_ctor_set(v___x_2366_, 0, v___x_2370_);
v___x_2372_ = v___x_2366_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2376_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2376_, 3, v_impl_2270_);
lean_ctor_set(v_reuseFailAlloc_2376_, 4, v_l_2360_);
v___x_2372_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_r_2361_);
lean_ctor_set(v___x_2267_, 3, v___x_2372_);
lean_ctor_set(v___x_2267_, 2, v_v_2364_);
lean_ctor_set(v___x_2267_, 1, v_k_2363_);
lean_ctor_set(v___x_2267_, 0, v___x_2369_);
v___x_2374_ = v___x_2267_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_k_2363_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_v_2364_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v_r_2361_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_k_2380_; lean_object* v_v_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2404_; 
v_k_2380_ = lean_ctor_get(v_r_2265_, 1);
v_v_2381_ = lean_ctor_get(v_r_2265_, 2);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_r_2265_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; lean_object* v_unused_2406_; lean_object* v_unused_2407_; 
v_unused_2405_ = lean_ctor_get(v_r_2265_, 4);
lean_dec(v_unused_2405_);
v_unused_2406_ = lean_ctor_get(v_r_2265_, 3);
lean_dec(v_unused_2406_);
v_unused_2407_ = lean_ctor_get(v_r_2265_, 0);
lean_dec(v_unused_2407_);
v___x_2383_ = v_r_2265_;
v_isShared_2384_ = v_isSharedCheck_2404_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_v_2381_);
lean_inc(v_k_2380_);
lean_dec(v_r_2265_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2404_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v_k_2385_; lean_object* v_v_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2400_; 
v_k_2385_ = lean_ctor_get(v_l_2360_, 1);
v_v_2386_ = lean_ctor_get(v_l_2360_, 2);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_l_2360_);
if (v_isSharedCheck_2400_ == 0)
{
lean_object* v_unused_2401_; lean_object* v_unused_2402_; lean_object* v_unused_2403_; 
v_unused_2401_ = lean_ctor_get(v_l_2360_, 4);
lean_dec(v_unused_2401_);
v_unused_2402_ = lean_ctor_get(v_l_2360_, 3);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_l_2360_, 0);
lean_dec(v_unused_2403_);
v___x_2388_ = v_l_2360_;
v_isShared_2389_ = v_isSharedCheck_2400_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_v_2386_);
lean_inc(v_k_2385_);
lean_dec(v_l_2360_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2400_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2392_; 
v___x_2390_ = lean_unsigned_to_nat(3u);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 4, v_r_2361_);
lean_ctor_set(v___x_2388_, 3, v_r_2361_);
lean_ctor_set(v___x_2388_, 2, v_v_2263_);
lean_ctor_set(v___x_2388_, 1, v_k_2262_);
lean_ctor_set(v___x_2388_, 0, v___x_2271_);
v___x_2392_ = v___x_2388_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2399_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2399_, 3, v_r_2361_);
lean_ctor_set(v_reuseFailAlloc_2399_, 4, v_r_2361_);
v___x_2392_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2394_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 3, v_r_2361_);
lean_ctor_set(v___x_2383_, 0, v___x_2271_);
v___x_2394_ = v___x_2383_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_k_2380_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_v_2381_);
lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_r_2361_);
lean_ctor_set(v_reuseFailAlloc_2398_, 4, v_r_2361_);
v___x_2394_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2396_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2394_);
lean_ctor_set(v___x_2267_, 3, v___x_2392_);
lean_ctor_set(v___x_2267_, 2, v_v_2386_);
lean_ctor_set(v___x_2267_, 1, v_k_2385_);
lean_ctor_set(v___x_2267_, 0, v___x_2390_);
v___x_2396_ = v___x_2267_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_k_2385_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_v_2386_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2408_; 
v_r_2408_ = lean_ctor_get(v_r_2265_, 4);
lean_inc(v_r_2408_);
if (lean_obj_tag(v_r_2408_) == 0)
{
lean_object* v_k_2409_; lean_object* v_v_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2421_; 
v_k_2409_ = lean_ctor_get(v_r_2265_, 1);
v_v_2410_ = lean_ctor_get(v_r_2265_, 2);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_r_2265_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; lean_object* v_unused_2423_; lean_object* v_unused_2424_; 
v_unused_2422_ = lean_ctor_get(v_r_2265_, 4);
lean_dec(v_unused_2422_);
v_unused_2423_ = lean_ctor_get(v_r_2265_, 3);
lean_dec(v_unused_2423_);
v_unused_2424_ = lean_ctor_get(v_r_2265_, 0);
lean_dec(v_unused_2424_);
v___x_2412_ = v_r_2265_;
v_isShared_2413_ = v_isSharedCheck_2421_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_v_2410_);
lean_inc(v_k_2409_);
lean_dec(v_r_2265_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2421_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = lean_unsigned_to_nat(3u);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 4, v_l_2360_);
lean_ctor_set(v___x_2412_, 2, v_v_2263_);
lean_ctor_set(v___x_2412_, 1, v_k_2262_);
lean_ctor_set(v___x_2412_, 0, v___x_2271_);
v___x_2416_ = v___x_2412_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2420_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2420_, 3, v_l_2360_);
lean_ctor_set(v_reuseFailAlloc_2420_, 4, v_l_2360_);
v___x_2416_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2418_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_r_2408_);
lean_ctor_set(v___x_2267_, 3, v___x_2416_);
lean_ctor_set(v___x_2267_, 2, v_v_2410_);
lean_ctor_set(v___x_2267_, 1, v_k_2409_);
lean_ctor_set(v___x_2267_, 0, v___x_2414_);
v___x_2418_ = v___x_2267_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2419_, 3, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2419_, 4, v_r_2408_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
else
{
lean_object* v_size_2425_; lean_object* v_k_2426_; lean_object* v_v_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2438_; 
v_size_2425_ = lean_ctor_get(v_r_2265_, 0);
v_k_2426_ = lean_ctor_get(v_r_2265_, 1);
v_v_2427_ = lean_ctor_get(v_r_2265_, 2);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_r_2265_);
if (v_isSharedCheck_2438_ == 0)
{
lean_object* v_unused_2439_; lean_object* v_unused_2440_; 
v_unused_2439_ = lean_ctor_get(v_r_2265_, 4);
lean_dec(v_unused_2439_);
v_unused_2440_ = lean_ctor_get(v_r_2265_, 3);
lean_dec(v_unused_2440_);
v___x_2429_ = v_r_2265_;
v_isShared_2430_ = v_isSharedCheck_2438_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_v_2427_);
lean_inc(v_k_2426_);
lean_inc(v_size_2425_);
lean_dec(v_r_2265_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2438_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 3, v_r_2408_);
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_size_2425_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_k_2426_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_v_2427_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_r_2408_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_r_2408_);
v___x_2432_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = lean_unsigned_to_nat(2u);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2432_);
lean_ctor_set(v___x_2267_, 3, v_r_2408_);
lean_ctor_set(v___x_2267_, 0, v___x_2433_);
v___x_2435_ = v___x_2267_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2436_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2436_, 3, v_r_2408_);
lean_ctor_set(v_reuseFailAlloc_2436_, 4, v___x_2432_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
}
else
{
lean_object* v___x_2442_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 3, v_r_2265_);
lean_ctor_set(v___x_2267_, 0, v___x_2271_);
v___x_2442_ = v___x_2267_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2443_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2443_, 3, v_r_2265_);
lean_ctor_set(v_reuseFailAlloc_2443_, 4, v_r_2265_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2267_);
lean_dec(v_v_2263_);
lean_dec(v_k_2262_);
if (lean_obj_tag(v_l_2264_) == 0)
{
if (lean_obj_tag(v_r_2265_) == 0)
{
lean_object* v_size_2444_; lean_object* v_k_2445_; lean_object* v_v_2446_; lean_object* v_l_2447_; lean_object* v_r_2448_; lean_object* v_size_2449_; lean_object* v_k_2450_; lean_object* v_v_2451_; lean_object* v_l_2452_; lean_object* v_r_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v_size_2444_ = lean_ctor_get(v_l_2264_, 0);
v_k_2445_ = lean_ctor_get(v_l_2264_, 1);
v_v_2446_ = lean_ctor_get(v_l_2264_, 2);
v_l_2447_ = lean_ctor_get(v_l_2264_, 3);
v_r_2448_ = lean_ctor_get(v_l_2264_, 4);
lean_inc(v_r_2448_);
v_size_2449_ = lean_ctor_get(v_r_2265_, 0);
v_k_2450_ = lean_ctor_get(v_r_2265_, 1);
v_v_2451_ = lean_ctor_get(v_r_2265_, 2);
v_l_2452_ = lean_ctor_get(v_r_2265_, 3);
lean_inc(v_l_2452_);
v_r_2453_ = lean_ctor_get(v_r_2265_, 4);
v___x_2454_ = lean_unsigned_to_nat(1u);
v___x_2455_ = lean_nat_dec_lt(v_size_2444_, v_size_2449_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2591_; 
lean_inc(v_l_2447_);
lean_inc(v_v_2446_);
lean_inc(v_k_2445_);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_l_2264_);
if (v_isSharedCheck_2591_ == 0)
{
lean_object* v_unused_2592_; lean_object* v_unused_2593_; lean_object* v_unused_2594_; lean_object* v_unused_2595_; lean_object* v_unused_2596_; 
v_unused_2592_ = lean_ctor_get(v_l_2264_, 4);
lean_dec(v_unused_2592_);
v_unused_2593_ = lean_ctor_get(v_l_2264_, 3);
lean_dec(v_unused_2593_);
v_unused_2594_ = lean_ctor_get(v_l_2264_, 2);
lean_dec(v_unused_2594_);
v_unused_2595_ = lean_ctor_get(v_l_2264_, 1);
lean_dec(v_unused_2595_);
v_unused_2596_ = lean_ctor_get(v_l_2264_, 0);
lean_dec(v_unused_2596_);
v___x_2457_ = v_l_2264_;
v_isShared_2458_ = v_isSharedCheck_2591_;
goto v_resetjp_2456_;
}
else
{
lean_dec(v_l_2264_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2591_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; lean_object* v_tree_2460_; 
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2445_, v_v_2446_, v_l_2447_, v_r_2448_);
v_tree_2460_ = lean_ctor_get(v___x_2459_, 2);
if (lean_obj_tag(v_tree_2460_) == 0)
{
lean_object* v_k_2461_; lean_object* v_v_2462_; lean_object* v_size_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; 
lean_inc_ref(v_tree_2460_);
v_k_2461_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_k_2461_);
v_v_2462_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_v_2462_);
lean_dec_ref(v___x_2459_);
v_size_2463_ = lean_ctor_get(v_tree_2460_, 0);
v___x_2464_ = lean_unsigned_to_nat(3u);
v___x_2465_ = lean_nat_mul(v___x_2464_, v_size_2463_);
v___x_2466_ = lean_nat_dec_lt(v___x_2465_, v_size_2449_);
lean_dec(v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
lean_dec(v_l_2452_);
v___x_2467_ = lean_nat_add(v___x_2454_, v_size_2463_);
v___x_2468_ = lean_nat_add(v___x_2467_, v_size_2449_);
lean_dec(v___x_2467_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v_r_2265_);
lean_ctor_set(v___x_2457_, 3, v_tree_2460_);
lean_ctor_set(v___x_2457_, 2, v_v_2462_);
lean_ctor_set(v___x_2457_, 1, v_k_2461_);
lean_ctor_set(v___x_2457_, 0, v___x_2468_);
v___x_2470_ = v___x_2457_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_k_2461_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_v_2462_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v_tree_2460_);
lean_ctor_set(v_reuseFailAlloc_2471_, 4, v_r_2265_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
else
{
lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2526_; 
lean_inc(v_r_2453_);
lean_inc(v_v_2451_);
lean_inc(v_k_2450_);
lean_inc(v_size_2449_);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_r_2265_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; lean_object* v_unused_2528_; lean_object* v_unused_2529_; lean_object* v_unused_2530_; lean_object* v_unused_2531_; 
v_unused_2527_ = lean_ctor_get(v_r_2265_, 4);
lean_dec(v_unused_2527_);
v_unused_2528_ = lean_ctor_get(v_r_2265_, 3);
lean_dec(v_unused_2528_);
v_unused_2529_ = lean_ctor_get(v_r_2265_, 2);
lean_dec(v_unused_2529_);
v_unused_2530_ = lean_ctor_get(v_r_2265_, 1);
lean_dec(v_unused_2530_);
v_unused_2531_ = lean_ctor_get(v_r_2265_, 0);
lean_dec(v_unused_2531_);
v___x_2473_ = v_r_2265_;
v_isShared_2474_ = v_isSharedCheck_2526_;
goto v_resetjp_2472_;
}
else
{
lean_dec(v_r_2265_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2526_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v_size_2475_; lean_object* v_k_2476_; lean_object* v_v_2477_; lean_object* v_l_2478_; lean_object* v_r_2479_; lean_object* v_size_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_size_2475_ = lean_ctor_get(v_l_2452_, 0);
v_k_2476_ = lean_ctor_get(v_l_2452_, 1);
v_v_2477_ = lean_ctor_get(v_l_2452_, 2);
v_l_2478_ = lean_ctor_get(v_l_2452_, 3);
v_r_2479_ = lean_ctor_get(v_l_2452_, 4);
v_size_2480_ = lean_ctor_get(v_r_2453_, 0);
v___x_2481_ = lean_unsigned_to_nat(2u);
v___x_2482_ = lean_nat_mul(v___x_2481_, v_size_2480_);
v___x_2483_ = lean_nat_dec_lt(v_size_2475_, v___x_2482_);
lean_dec(v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2511_; 
lean_inc(v_r_2479_);
lean_inc(v_l_2478_);
lean_inc(v_v_2477_);
lean_inc(v_k_2476_);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_l_2452_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; lean_object* v_unused_2513_; lean_object* v_unused_2514_; lean_object* v_unused_2515_; lean_object* v_unused_2516_; 
v_unused_2512_ = lean_ctor_get(v_l_2452_, 4);
lean_dec(v_unused_2512_);
v_unused_2513_ = lean_ctor_get(v_l_2452_, 3);
lean_dec(v_unused_2513_);
v_unused_2514_ = lean_ctor_get(v_l_2452_, 2);
lean_dec(v_unused_2514_);
v_unused_2515_ = lean_ctor_get(v_l_2452_, 1);
lean_dec(v_unused_2515_);
v_unused_2516_ = lean_ctor_get(v_l_2452_, 0);
lean_dec(v_unused_2516_);
v___x_2485_ = v_l_2452_;
v_isShared_2486_ = v_isSharedCheck_2511_;
goto v_resetjp_2484_;
}
else
{
lean_dec(v_l_2452_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2511_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2501_; 
v___x_2487_ = lean_nat_add(v___x_2454_, v_size_2463_);
v___x_2488_ = lean_nat_add(v___x_2487_, v_size_2449_);
lean_dec(v_size_2449_);
if (lean_obj_tag(v_l_2478_) == 0)
{
lean_object* v_size_2509_; 
v_size_2509_ = lean_ctor_get(v_l_2478_, 0);
lean_inc(v_size_2509_);
v___y_2501_ = v_size_2509_;
goto v___jp_2500_;
}
else
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_unsigned_to_nat(0u);
v___y_2501_ = v___x_2510_;
goto v___jp_2500_;
}
v___jp_2489_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2493_ = lean_nat_add(v___y_2490_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec(v___y_2490_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 4, v_r_2453_);
lean_ctor_set(v___x_2485_, 3, v_r_2479_);
lean_ctor_set(v___x_2485_, 2, v_v_2451_);
lean_ctor_set(v___x_2485_, 1, v_k_2450_);
lean_ctor_set(v___x_2485_, 0, v___x_2493_);
v___x_2495_ = v___x_2485_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_k_2450_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_v_2451_);
lean_ctor_set(v_reuseFailAlloc_2499_, 3, v_r_2479_);
lean_ctor_set(v_reuseFailAlloc_2499_, 4, v_r_2453_);
v___x_2495_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2497_; 
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 4, v___x_2495_);
lean_ctor_set(v___x_2473_, 3, v___y_2491_);
lean_ctor_set(v___x_2473_, 2, v_v_2477_);
lean_ctor_set(v___x_2473_, 1, v_k_2476_);
lean_ctor_set(v___x_2473_, 0, v___x_2488_);
v___x_2497_ = v___x_2473_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_k_2476_);
lean_ctor_set(v_reuseFailAlloc_2498_, 2, v_v_2477_);
lean_ctor_set(v_reuseFailAlloc_2498_, 3, v___y_2491_);
lean_ctor_set(v_reuseFailAlloc_2498_, 4, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
v___jp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2502_ = lean_nat_add(v___x_2487_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec(v___x_2487_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v_l_2478_);
lean_ctor_set(v___x_2457_, 3, v_tree_2460_);
lean_ctor_set(v___x_2457_, 2, v_v_2462_);
lean_ctor_set(v___x_2457_, 1, v_k_2461_);
lean_ctor_set(v___x_2457_, 0, v___x_2502_);
v___x_2504_ = v___x_2457_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_k_2461_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_v_2462_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v_tree_2460_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v_l_2478_);
v___x_2504_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_nat_add(v___x_2454_, v_size_2480_);
if (lean_obj_tag(v_r_2479_) == 0)
{
lean_object* v_size_2506_; 
v_size_2506_ = lean_ctor_get(v_r_2479_, 0);
lean_inc(v_size_2506_);
v___y_2490_ = v___x_2505_;
v___y_2491_ = v___x_2504_;
v___y_2492_ = v_size_2506_;
goto v___jp_2489_;
}
else
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_unsigned_to_nat(0u);
v___y_2490_ = v___x_2505_;
v___y_2491_ = v___x_2504_;
v___y_2492_ = v___x_2507_;
goto v___jp_2489_;
}
}
}
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
v___x_2517_ = lean_nat_add(v___x_2454_, v_size_2463_);
v___x_2518_ = lean_nat_add(v___x_2517_, v_size_2449_);
lean_dec(v_size_2449_);
v___x_2519_ = lean_nat_add(v___x_2517_, v_size_2475_);
lean_dec(v___x_2517_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 4, v_l_2452_);
lean_ctor_set(v___x_2473_, 3, v_tree_2460_);
lean_ctor_set(v___x_2473_, 2, v_v_2462_);
lean_ctor_set(v___x_2473_, 1, v_k_2461_);
lean_ctor_set(v___x_2473_, 0, v___x_2519_);
v___x_2521_ = v___x_2473_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_k_2461_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_v_2462_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v_tree_2460_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v_l_2452_);
v___x_2521_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2523_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v_r_2453_);
lean_ctor_set(v___x_2457_, 3, v___x_2521_);
lean_ctor_set(v___x_2457_, 2, v_v_2451_);
lean_ctor_set(v___x_2457_, 1, v_k_2450_);
lean_ctor_set(v___x_2457_, 0, v___x_2518_);
v___x_2523_ = v___x_2457_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_k_2450_);
lean_ctor_set(v_reuseFailAlloc_2524_, 2, v_v_2451_);
lean_ctor_set(v_reuseFailAlloc_2524_, 3, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2524_, 4, v_r_2453_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
else
{
lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2585_; 
lean_inc(v_r_2453_);
lean_inc(v_v_2451_);
lean_inc(v_k_2450_);
lean_inc(v_size_2449_);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_r_2265_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; lean_object* v_unused_2587_; lean_object* v_unused_2588_; lean_object* v_unused_2589_; lean_object* v_unused_2590_; 
v_unused_2586_ = lean_ctor_get(v_r_2265_, 4);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_r_2265_, 3);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v_r_2265_, 2);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v_r_2265_, 1);
lean_dec(v_unused_2589_);
v_unused_2590_ = lean_ctor_get(v_r_2265_, 0);
lean_dec(v_unused_2590_);
v___x_2533_ = v_r_2265_;
v_isShared_2534_ = v_isSharedCheck_2585_;
goto v_resetjp_2532_;
}
else
{
lean_dec(v_r_2265_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2585_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
if (lean_obj_tag(v_l_2452_) == 0)
{
if (lean_obj_tag(v_r_2453_) == 0)
{
lean_object* v_k_2535_; lean_object* v_v_2536_; lean_object* v_size_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
lean_inc(v_tree_2460_);
v_k_2535_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_k_2535_);
v_v_2536_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_v_2536_);
lean_dec_ref(v___x_2459_);
v_size_2537_ = lean_ctor_get(v_l_2452_, 0);
v___x_2538_ = lean_nat_add(v___x_2454_, v_size_2449_);
lean_dec(v_size_2449_);
v___x_2539_ = lean_nat_add(v___x_2454_, v_size_2537_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 4, v_l_2452_);
lean_ctor_set(v___x_2533_, 3, v_tree_2460_);
lean_ctor_set(v___x_2533_, 2, v_v_2536_);
lean_ctor_set(v___x_2533_, 1, v_k_2535_);
lean_ctor_set(v___x_2533_, 0, v___x_2539_);
v___x_2541_ = v___x_2533_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_k_2535_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_v_2536_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v_tree_2460_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v_l_2452_);
v___x_2541_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2543_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v_r_2453_);
lean_ctor_set(v___x_2457_, 3, v___x_2541_);
lean_ctor_set(v___x_2457_, 2, v_v_2451_);
lean_ctor_set(v___x_2457_, 1, v_k_2450_);
lean_ctor_set(v___x_2457_, 0, v___x_2538_);
v___x_2543_ = v___x_2457_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_k_2450_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v_v_2451_);
lean_ctor_set(v_reuseFailAlloc_2544_, 3, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2544_, 4, v_r_2453_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
else
{
lean_object* v_k_2546_; lean_object* v_v_2547_; lean_object* v_k_2548_; lean_object* v_v_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_size_2449_);
v_k_2546_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_k_2546_);
v_v_2547_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_v_2547_);
lean_dec_ref(v___x_2459_);
v_k_2548_ = lean_ctor_get(v_l_2452_, 1);
v_v_2549_ = lean_ctor_get(v_l_2452_, 2);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_l_2452_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; lean_object* v_unused_2565_; lean_object* v_unused_2566_; 
v_unused_2564_ = lean_ctor_get(v_l_2452_, 4);
lean_dec(v_unused_2564_);
v_unused_2565_ = lean_ctor_get(v_l_2452_, 3);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_l_2452_, 0);
lean_dec(v_unused_2566_);
v___x_2551_ = v_l_2452_;
v_isShared_2552_ = v_isSharedCheck_2563_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_v_2549_);
lean_inc(v_k_2548_);
lean_dec(v_l_2452_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2563_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2553_ = lean_unsigned_to_nat(3u);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 4, v_r_2453_);
lean_ctor_set(v___x_2551_, 3, v_r_2453_);
lean_ctor_set(v___x_2551_, 2, v_v_2547_);
lean_ctor_set(v___x_2551_, 1, v_k_2546_);
lean_ctor_set(v___x_2551_, 0, v___x_2454_);
v___x_2555_ = v___x_2551_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_k_2546_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_v_2547_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_r_2453_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_r_2453_);
v___x_2555_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2557_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 3, v_r_2453_);
lean_ctor_set(v___x_2533_, 0, v___x_2454_);
v___x_2557_ = v___x_2533_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_k_2450_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_v_2451_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_r_2453_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_r_2453_);
v___x_2557_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2559_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v___x_2557_);
lean_ctor_set(v___x_2457_, 3, v___x_2555_);
lean_ctor_set(v___x_2457_, 2, v_v_2549_);
lean_ctor_set(v___x_2457_, 1, v_k_2548_);
lean_ctor_set(v___x_2457_, 0, v___x_2553_);
v___x_2559_ = v___x_2457_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_2560_, 3, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2560_, 4, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2453_) == 0)
{
lean_object* v_k_2567_; lean_object* v_v_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
lean_dec(v_size_2449_);
v_k_2567_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_k_2567_);
v_v_2568_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_v_2568_);
lean_dec_ref(v___x_2459_);
v___x_2569_ = lean_unsigned_to_nat(3u);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 4, v_l_2452_);
lean_ctor_set(v___x_2533_, 2, v_v_2568_);
lean_ctor_set(v___x_2533_, 1, v_k_2567_);
lean_ctor_set(v___x_2533_, 0, v___x_2454_);
v___x_2571_ = v___x_2533_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_k_2567_);
lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_v_2568_);
lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_l_2452_);
lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_l_2452_);
v___x_2571_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2573_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v_r_2453_);
lean_ctor_set(v___x_2457_, 3, v___x_2571_);
lean_ctor_set(v___x_2457_, 2, v_v_2451_);
lean_ctor_set(v___x_2457_, 1, v_k_2450_);
lean_ctor_set(v___x_2457_, 0, v___x_2569_);
v___x_2573_ = v___x_2457_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_k_2450_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v_v_2451_);
lean_ctor_set(v_reuseFailAlloc_2574_, 3, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2574_, 4, v_r_2453_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
else
{
lean_object* v_k_2576_; lean_object* v_v_2577_; lean_object* v___x_2579_; 
v_k_2576_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_k_2576_);
v_v_2577_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_v_2577_);
lean_dec_ref(v___x_2459_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 3, v_r_2453_);
v___x_2579_ = v___x_2533_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_size_2449_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_k_2450_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_v_2451_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_r_2453_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_r_2453_);
v___x_2579_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_unsigned_to_nat(2u);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v___x_2579_);
lean_ctor_set(v___x_2457_, 3, v_r_2453_);
lean_ctor_set(v___x_2457_, 2, v_v_2577_);
lean_ctor_set(v___x_2457_, 1, v_k_2576_);
lean_ctor_set(v___x_2457_, 0, v___x_2580_);
v___x_2582_ = v___x_2457_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_k_2576_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_v_2577_);
lean_ctor_set(v_reuseFailAlloc_2583_, 3, v_r_2453_);
lean_ctor_set(v_reuseFailAlloc_2583_, 4, v___x_2579_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
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
lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2749_; 
lean_inc(v_r_2453_);
lean_inc(v_v_2451_);
lean_inc(v_k_2450_);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_r_2265_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; lean_object* v_unused_2753_; lean_object* v_unused_2754_; 
v_unused_2750_ = lean_ctor_get(v_r_2265_, 4);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_r_2265_, 3);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_r_2265_, 2);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v_r_2265_, 1);
lean_dec(v_unused_2753_);
v_unused_2754_ = lean_ctor_get(v_r_2265_, 0);
lean_dec(v_unused_2754_);
v___x_2598_ = v_r_2265_;
v_isShared_2599_ = v_isSharedCheck_2749_;
goto v_resetjp_2597_;
}
else
{
lean_dec(v_r_2265_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2749_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v_tree_2601_; 
v___x_2600_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2450_, v_v_2451_, v_l_2452_, v_r_2453_);
v_tree_2601_ = lean_ctor_get(v___x_2600_, 2);
lean_inc(v_tree_2601_);
if (lean_obj_tag(v_tree_2601_) == 0)
{
lean_object* v_k_2602_; lean_object* v_v_2603_; lean_object* v_size_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v_k_2602_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_k_2602_);
v_v_2603_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_v_2603_);
lean_dec_ref(v___x_2600_);
v_size_2604_ = lean_ctor_get(v_tree_2601_, 0);
v___x_2605_ = lean_unsigned_to_nat(3u);
v___x_2606_ = lean_nat_mul(v___x_2605_, v_size_2604_);
v___x_2607_ = lean_nat_dec_lt(v___x_2606_, v_size_2444_);
lean_dec(v___x_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
lean_dec(v_r_2448_);
v___x_2608_ = lean_nat_add(v___x_2454_, v_size_2444_);
v___x_2609_ = lean_nat_add(v___x_2608_, v_size_2604_);
lean_dec(v___x_2608_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 4, v_tree_2601_);
lean_ctor_set(v___x_2598_, 3, v_l_2264_);
lean_ctor_set(v___x_2598_, 2, v_v_2603_);
lean_ctor_set(v___x_2598_, 1, v_k_2602_);
lean_ctor_set(v___x_2598_, 0, v___x_2609_);
v___x_2611_ = v___x_2598_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_k_2602_);
lean_ctor_set(v_reuseFailAlloc_2612_, 2, v_v_2603_);
lean_ctor_set(v_reuseFailAlloc_2612_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2612_, 4, v_tree_2601_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
else
{
lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2678_; 
lean_inc(v_l_2447_);
lean_inc(v_v_2446_);
lean_inc(v_k_2445_);
lean_inc(v_size_2444_);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_l_2264_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; lean_object* v_unused_2680_; lean_object* v_unused_2681_; lean_object* v_unused_2682_; lean_object* v_unused_2683_; 
v_unused_2679_ = lean_ctor_get(v_l_2264_, 4);
lean_dec(v_unused_2679_);
v_unused_2680_ = lean_ctor_get(v_l_2264_, 3);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_l_2264_, 2);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_l_2264_, 1);
lean_dec(v_unused_2682_);
v_unused_2683_ = lean_ctor_get(v_l_2264_, 0);
lean_dec(v_unused_2683_);
v___x_2614_ = v_l_2264_;
v_isShared_2615_ = v_isSharedCheck_2678_;
goto v_resetjp_2613_;
}
else
{
lean_dec(v_l_2264_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2678_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v_size_2616_; lean_object* v_size_2617_; lean_object* v_k_2618_; lean_object* v_v_2619_; lean_object* v_l_2620_; lean_object* v_r_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v_size_2616_ = lean_ctor_get(v_l_2447_, 0);
v_size_2617_ = lean_ctor_get(v_r_2448_, 0);
v_k_2618_ = lean_ctor_get(v_r_2448_, 1);
v_v_2619_ = lean_ctor_get(v_r_2448_, 2);
v_l_2620_ = lean_ctor_get(v_r_2448_, 3);
v_r_2621_ = lean_ctor_get(v_r_2448_, 4);
v___x_2622_ = lean_unsigned_to_nat(2u);
v___x_2623_ = lean_nat_mul(v___x_2622_, v_size_2616_);
v___x_2624_ = lean_nat_dec_lt(v_size_2617_, v___x_2623_);
lean_dec(v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2662_; 
lean_inc(v_r_2621_);
lean_inc(v_l_2620_);
lean_inc(v_v_2619_);
lean_inc(v_k_2618_);
lean_del_object(v___x_2614_);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_r_2448_);
if (v_isSharedCheck_2662_ == 0)
{
lean_object* v_unused_2663_; lean_object* v_unused_2664_; lean_object* v_unused_2665_; lean_object* v_unused_2666_; lean_object* v_unused_2667_; 
v_unused_2663_ = lean_ctor_get(v_r_2448_, 4);
lean_dec(v_unused_2663_);
v_unused_2664_ = lean_ctor_get(v_r_2448_, 3);
lean_dec(v_unused_2664_);
v_unused_2665_ = lean_ctor_get(v_r_2448_, 2);
lean_dec(v_unused_2665_);
v_unused_2666_ = lean_ctor_get(v_r_2448_, 1);
lean_dec(v_unused_2666_);
v_unused_2667_ = lean_ctor_get(v_r_2448_, 0);
lean_dec(v_unused_2667_);
v___x_2626_ = v_r_2448_;
v_isShared_2627_ = v_isSharedCheck_2662_;
goto v_resetjp_2625_;
}
else
{
lean_dec(v_r_2448_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2662_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___x_2650_; lean_object* v___y_2652_; 
v___x_2628_ = lean_nat_add(v___x_2454_, v_size_2444_);
lean_dec(v_size_2444_);
v___x_2629_ = lean_nat_add(v___x_2628_, v_size_2604_);
lean_dec(v___x_2628_);
v___x_2650_ = lean_nat_add(v___x_2454_, v_size_2616_);
if (lean_obj_tag(v_l_2620_) == 0)
{
lean_object* v_size_2660_; 
v_size_2660_ = lean_ctor_get(v_l_2620_, 0);
lean_inc(v_size_2660_);
v___y_2652_ = v_size_2660_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2661_; 
v___x_2661_ = lean_unsigned_to_nat(0u);
v___y_2652_ = v___x_2661_;
goto v___jp_2651_;
}
v___jp_2630_:
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2634_ = lean_nat_add(v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec(v___y_2632_);
lean_inc_ref(v_tree_2601_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 4, v_tree_2601_);
lean_ctor_set(v___x_2626_, 3, v_r_2621_);
lean_ctor_set(v___x_2626_, 2, v_v_2603_);
lean_ctor_set(v___x_2626_, 1, v_k_2602_);
lean_ctor_set(v___x_2626_, 0, v___x_2634_);
v___x_2636_ = v___x_2626_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_k_2602_);
lean_ctor_set(v_reuseFailAlloc_2649_, 2, v_v_2603_);
lean_ctor_set(v_reuseFailAlloc_2649_, 3, v_r_2621_);
lean_ctor_set(v_reuseFailAlloc_2649_, 4, v_tree_2601_);
v___x_2636_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
v_isSharedCheck_2643_ = !lean_is_exclusive(v_tree_2601_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; lean_object* v_unused_2645_; lean_object* v_unused_2646_; lean_object* v_unused_2647_; lean_object* v_unused_2648_; 
v_unused_2644_ = lean_ctor_get(v_tree_2601_, 4);
lean_dec(v_unused_2644_);
v_unused_2645_ = lean_ctor_get(v_tree_2601_, 3);
lean_dec(v_unused_2645_);
v_unused_2646_ = lean_ctor_get(v_tree_2601_, 2);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_tree_2601_, 1);
lean_dec(v_unused_2647_);
v_unused_2648_ = lean_ctor_get(v_tree_2601_, 0);
lean_dec(v_unused_2648_);
v___x_2638_ = v_tree_2601_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_dec(v_tree_2601_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 4, v___x_2636_);
lean_ctor_set(v___x_2638_, 3, v___y_2631_);
lean_ctor_set(v___x_2638_, 2, v_v_2619_);
lean_ctor_set(v___x_2638_, 1, v_k_2618_);
lean_ctor_set(v___x_2638_, 0, v___x_2629_);
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2629_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_k_2618_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_v_2619_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v___y_2631_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v___x_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
v___jp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2653_ = lean_nat_add(v___x_2650_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec(v___x_2650_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 4, v_l_2620_);
lean_ctor_set(v___x_2598_, 3, v_l_2447_);
lean_ctor_set(v___x_2598_, 2, v_v_2446_);
lean_ctor_set(v___x_2598_, 1, v_k_2445_);
lean_ctor_set(v___x_2598_, 0, v___x_2653_);
v___x_2655_ = v___x_2598_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_k_2445_);
lean_ctor_set(v_reuseFailAlloc_2659_, 2, v_v_2446_);
lean_ctor_set(v_reuseFailAlloc_2659_, 3, v_l_2447_);
lean_ctor_set(v_reuseFailAlloc_2659_, 4, v_l_2620_);
v___x_2655_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_nat_add(v___x_2454_, v_size_2604_);
if (lean_obj_tag(v_r_2621_) == 0)
{
lean_object* v_size_2657_; 
v_size_2657_ = lean_ctor_get(v_r_2621_, 0);
lean_inc(v_size_2657_);
v___y_2631_ = v___x_2655_;
v___y_2632_ = v___x_2656_;
v___y_2633_ = v_size_2657_;
goto v___jp_2630_;
}
else
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_unsigned_to_nat(0u);
v___y_2631_ = v___x_2655_;
v___y_2632_ = v___x_2656_;
v___y_2633_ = v___x_2658_;
goto v___jp_2630_;
}
}
}
}
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2668_ = lean_nat_add(v___x_2454_, v_size_2444_);
lean_dec(v_size_2444_);
v___x_2669_ = lean_nat_add(v___x_2668_, v_size_2604_);
lean_dec(v___x_2668_);
v___x_2670_ = lean_nat_add(v___x_2454_, v_size_2604_);
v___x_2671_ = lean_nat_add(v___x_2670_, v_size_2617_);
lean_dec(v___x_2670_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 4, v_tree_2601_);
lean_ctor_set(v___x_2598_, 3, v_r_2448_);
lean_ctor_set(v___x_2598_, 2, v_v_2603_);
lean_ctor_set(v___x_2598_, 1, v_k_2602_);
lean_ctor_set(v___x_2598_, 0, v___x_2671_);
v___x_2673_ = v___x_2598_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_k_2602_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_v_2603_);
lean_ctor_set(v_reuseFailAlloc_2677_, 3, v_r_2448_);
lean_ctor_set(v_reuseFailAlloc_2677_, 4, v_tree_2601_);
v___x_2673_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2675_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 4, v___x_2673_);
lean_ctor_set(v___x_2614_, 0, v___x_2669_);
v___x_2675_ = v___x_2614_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_k_2445_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v_v_2446_);
lean_ctor_set(v_reuseFailAlloc_2676_, 3, v_l_2447_);
lean_ctor_set(v_reuseFailAlloc_2676_, 4, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2447_) == 0)
{
lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2707_; 
lean_inc_ref(v_l_2447_);
lean_inc(v_v_2446_);
lean_inc(v_k_2445_);
lean_inc(v_size_2444_);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_l_2264_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; lean_object* v_unused_2709_; lean_object* v_unused_2710_; lean_object* v_unused_2711_; lean_object* v_unused_2712_; 
v_unused_2708_ = lean_ctor_get(v_l_2264_, 4);
lean_dec(v_unused_2708_);
v_unused_2709_ = lean_ctor_get(v_l_2264_, 3);
lean_dec(v_unused_2709_);
v_unused_2710_ = lean_ctor_get(v_l_2264_, 2);
lean_dec(v_unused_2710_);
v_unused_2711_ = lean_ctor_get(v_l_2264_, 1);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_l_2264_, 0);
lean_dec(v_unused_2712_);
v___x_2685_ = v_l_2264_;
v_isShared_2686_ = v_isSharedCheck_2707_;
goto v_resetjp_2684_;
}
else
{
lean_dec(v_l_2264_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2707_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
if (lean_obj_tag(v_r_2448_) == 0)
{
lean_object* v_k_2687_; lean_object* v_v_2688_; lean_object* v_size_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
v_k_2687_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_k_2687_);
v_v_2688_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_v_2688_);
lean_dec_ref(v___x_2600_);
v_size_2689_ = lean_ctor_get(v_r_2448_, 0);
v___x_2690_ = lean_nat_add(v___x_2454_, v_size_2444_);
lean_dec(v_size_2444_);
v___x_2691_ = lean_nat_add(v___x_2454_, v_size_2689_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 4, v_tree_2601_);
lean_ctor_set(v___x_2598_, 3, v_r_2448_);
lean_ctor_set(v___x_2598_, 2, v_v_2688_);
lean_ctor_set(v___x_2598_, 1, v_k_2687_);
lean_ctor_set(v___x_2598_, 0, v___x_2691_);
v___x_2693_ = v___x_2598_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_k_2687_);
lean_ctor_set(v_reuseFailAlloc_2697_, 2, v_v_2688_);
lean_ctor_set(v_reuseFailAlloc_2697_, 3, v_r_2448_);
lean_ctor_set(v_reuseFailAlloc_2697_, 4, v_tree_2601_);
v___x_2693_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2695_; 
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 4, v___x_2693_);
lean_ctor_set(v___x_2685_, 0, v___x_2690_);
v___x_2695_ = v___x_2685_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_k_2445_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_v_2446_);
lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_l_2447_);
lean_ctor_set(v_reuseFailAlloc_2696_, 4, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
else
{
lean_object* v_k_2698_; lean_object* v_v_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
lean_dec(v_size_2444_);
v_k_2698_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_k_2698_);
v_v_2699_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_v_2699_);
lean_dec_ref(v___x_2600_);
v___x_2700_ = lean_unsigned_to_nat(3u);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 4, v_r_2448_);
lean_ctor_set(v___x_2598_, 3, v_r_2448_);
lean_ctor_set(v___x_2598_, 2, v_v_2699_);
lean_ctor_set(v___x_2598_, 1, v_k_2698_);
lean_ctor_set(v___x_2598_, 0, v___x_2454_);
v___x_2702_ = v___x_2598_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_k_2698_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_v_2699_);
lean_ctor_set(v_reuseFailAlloc_2706_, 3, v_r_2448_);
lean_ctor_set(v_reuseFailAlloc_2706_, 4, v_r_2448_);
v___x_2702_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2704_; 
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 4, v___x_2702_);
lean_ctor_set(v___x_2685_, 0, v___x_2700_);
v___x_2704_ = v___x_2685_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_k_2445_);
lean_ctor_set(v_reuseFailAlloc_2705_, 2, v_v_2446_);
lean_ctor_set(v_reuseFailAlloc_2705_, 3, v_l_2447_);
lean_ctor_set(v_reuseFailAlloc_2705_, 4, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2448_) == 0)
{
lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2737_; 
lean_inc(v_l_2447_);
lean_inc(v_v_2446_);
lean_inc(v_k_2445_);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_l_2264_);
if (v_isSharedCheck_2737_ == 0)
{
lean_object* v_unused_2738_; lean_object* v_unused_2739_; lean_object* v_unused_2740_; lean_object* v_unused_2741_; lean_object* v_unused_2742_; 
v_unused_2738_ = lean_ctor_get(v_l_2264_, 4);
lean_dec(v_unused_2738_);
v_unused_2739_ = lean_ctor_get(v_l_2264_, 3);
lean_dec(v_unused_2739_);
v_unused_2740_ = lean_ctor_get(v_l_2264_, 2);
lean_dec(v_unused_2740_);
v_unused_2741_ = lean_ctor_get(v_l_2264_, 1);
lean_dec(v_unused_2741_);
v_unused_2742_ = lean_ctor_get(v_l_2264_, 0);
lean_dec(v_unused_2742_);
v___x_2714_ = v_l_2264_;
v_isShared_2715_ = v_isSharedCheck_2737_;
goto v_resetjp_2713_;
}
else
{
lean_dec(v_l_2264_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2737_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v_k_2716_; lean_object* v_v_2717_; lean_object* v_k_2718_; lean_object* v_v_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2733_; 
v_k_2716_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_k_2716_);
v_v_2717_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_v_2717_);
lean_dec_ref(v___x_2600_);
v_k_2718_ = lean_ctor_get(v_r_2448_, 1);
v_v_2719_ = lean_ctor_get(v_r_2448_, 2);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_r_2448_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; lean_object* v_unused_2735_; lean_object* v_unused_2736_; 
v_unused_2734_ = lean_ctor_get(v_r_2448_, 4);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_r_2448_, 3);
lean_dec(v_unused_2735_);
v_unused_2736_ = lean_ctor_get(v_r_2448_, 0);
lean_dec(v_unused_2736_);
v___x_2721_ = v_r_2448_;
v_isShared_2722_ = v_isSharedCheck_2733_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_v_2719_);
lean_inc(v_k_2718_);
lean_dec(v_r_2448_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2733_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2723_ = lean_unsigned_to_nat(3u);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 4, v_l_2447_);
lean_ctor_set(v___x_2721_, 3, v_l_2447_);
lean_ctor_set(v___x_2721_, 2, v_v_2446_);
lean_ctor_set(v___x_2721_, 1, v_k_2445_);
lean_ctor_set(v___x_2721_, 0, v___x_2454_);
v___x_2725_ = v___x_2721_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_k_2445_);
lean_ctor_set(v_reuseFailAlloc_2732_, 2, v_v_2446_);
lean_ctor_set(v_reuseFailAlloc_2732_, 3, v_l_2447_);
lean_ctor_set(v_reuseFailAlloc_2732_, 4, v_l_2447_);
v___x_2725_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
lean_object* v___x_2727_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 4, v_l_2447_);
lean_ctor_set(v___x_2598_, 3, v_l_2447_);
lean_ctor_set(v___x_2598_, 2, v_v_2717_);
lean_ctor_set(v___x_2598_, 1, v_k_2716_);
lean_ctor_set(v___x_2598_, 0, v___x_2454_);
v___x_2727_ = v___x_2598_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_k_2716_);
lean_ctor_set(v_reuseFailAlloc_2731_, 2, v_v_2717_);
lean_ctor_set(v_reuseFailAlloc_2731_, 3, v_l_2447_);
lean_ctor_set(v_reuseFailAlloc_2731_, 4, v_l_2447_);
v___x_2727_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2729_; 
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 4, v___x_2727_);
lean_ctor_set(v___x_2714_, 3, v___x_2725_);
lean_ctor_set(v___x_2714_, 2, v_v_2719_);
lean_ctor_set(v___x_2714_, 1, v_k_2718_);
lean_ctor_set(v___x_2714_, 0, v___x_2723_);
v___x_2729_ = v___x_2714_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2723_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_k_2718_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_v_2719_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
}
else
{
lean_object* v_k_2743_; lean_object* v_v_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v_k_2743_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_k_2743_);
v_v_2744_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_v_2744_);
lean_dec_ref(v___x_2600_);
v___x_2745_ = lean_unsigned_to_nat(2u);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 4, v_r_2448_);
lean_ctor_set(v___x_2598_, 3, v_l_2264_);
lean_ctor_set(v___x_2598_, 2, v_v_2744_);
lean_ctor_set(v___x_2598_, 1, v_k_2743_);
lean_ctor_set(v___x_2598_, 0, v___x_2745_);
v___x_2747_ = v___x_2598_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_k_2743_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_v_2744_);
lean_ctor_set(v_reuseFailAlloc_2748_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2748_, 4, v_r_2448_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
}
}
else
{
return v_l_2264_;
}
}
else
{
return v_r_2265_;
}
}
default: 
{
lean_object* v_impl_2755_; lean_object* v___x_2756_; 
v_impl_2755_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2260_, v_r_2265_);
v___x_2756_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2755_) == 0)
{
if (lean_obj_tag(v_l_2264_) == 0)
{
lean_object* v_size_2757_; lean_object* v_size_2758_; lean_object* v_k_2759_; lean_object* v_v_2760_; lean_object* v_l_2761_; lean_object* v_r_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_size_2757_ = lean_ctor_get(v_impl_2755_, 0);
v_size_2758_ = lean_ctor_get(v_l_2264_, 0);
v_k_2759_ = lean_ctor_get(v_l_2264_, 1);
v_v_2760_ = lean_ctor_get(v_l_2264_, 2);
v_l_2761_ = lean_ctor_get(v_l_2264_, 3);
v_r_2762_ = lean_ctor_get(v_l_2264_, 4);
lean_inc(v_r_2762_);
v___x_2763_ = lean_unsigned_to_nat(3u);
v___x_2764_ = lean_nat_mul(v___x_2763_, v_size_2757_);
v___x_2765_ = lean_nat_dec_lt(v___x_2764_, v_size_2758_);
lean_dec(v___x_2764_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
lean_dec(v_r_2762_);
v___x_2766_ = lean_nat_add(v___x_2756_, v_size_2758_);
v___x_2767_ = lean_nat_add(v___x_2766_, v_size_2757_);
lean_dec(v___x_2766_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_impl_2755_);
lean_ctor_set(v___x_2267_, 0, v___x_2767_);
v___x_2769_ = v___x_2267_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2767_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2770_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2770_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2770_, 4, v_impl_2755_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
else
{
lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2836_; 
lean_inc(v_l_2761_);
lean_inc(v_v_2760_);
lean_inc(v_k_2759_);
lean_inc(v_size_2758_);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_l_2264_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; lean_object* v_unused_2838_; lean_object* v_unused_2839_; lean_object* v_unused_2840_; lean_object* v_unused_2841_; 
v_unused_2837_ = lean_ctor_get(v_l_2264_, 4);
lean_dec(v_unused_2837_);
v_unused_2838_ = lean_ctor_get(v_l_2264_, 3);
lean_dec(v_unused_2838_);
v_unused_2839_ = lean_ctor_get(v_l_2264_, 2);
lean_dec(v_unused_2839_);
v_unused_2840_ = lean_ctor_get(v_l_2264_, 1);
lean_dec(v_unused_2840_);
v_unused_2841_ = lean_ctor_get(v_l_2264_, 0);
lean_dec(v_unused_2841_);
v___x_2772_ = v_l_2264_;
v_isShared_2773_ = v_isSharedCheck_2836_;
goto v_resetjp_2771_;
}
else
{
lean_dec(v_l_2264_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2836_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v_size_2774_; lean_object* v_size_2775_; lean_object* v_k_2776_; lean_object* v_v_2777_; lean_object* v_l_2778_; lean_object* v_r_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v_size_2774_ = lean_ctor_get(v_l_2761_, 0);
v_size_2775_ = lean_ctor_get(v_r_2762_, 0);
v_k_2776_ = lean_ctor_get(v_r_2762_, 1);
v_v_2777_ = lean_ctor_get(v_r_2762_, 2);
v_l_2778_ = lean_ctor_get(v_r_2762_, 3);
v_r_2779_ = lean_ctor_get(v_r_2762_, 4);
v___x_2780_ = lean_unsigned_to_nat(2u);
v___x_2781_ = lean_nat_mul(v___x_2780_, v_size_2774_);
v___x_2782_ = lean_nat_dec_lt(v_size_2775_, v___x_2781_);
lean_dec(v___x_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2811_; 
lean_inc(v_r_2779_);
lean_inc(v_l_2778_);
lean_inc(v_v_2777_);
lean_inc(v_k_2776_);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_r_2762_);
if (v_isSharedCheck_2811_ == 0)
{
lean_object* v_unused_2812_; lean_object* v_unused_2813_; lean_object* v_unused_2814_; lean_object* v_unused_2815_; lean_object* v_unused_2816_; 
v_unused_2812_ = lean_ctor_get(v_r_2762_, 4);
lean_dec(v_unused_2812_);
v_unused_2813_ = lean_ctor_get(v_r_2762_, 3);
lean_dec(v_unused_2813_);
v_unused_2814_ = lean_ctor_get(v_r_2762_, 2);
lean_dec(v_unused_2814_);
v_unused_2815_ = lean_ctor_get(v_r_2762_, 1);
lean_dec(v_unused_2815_);
v_unused_2816_ = lean_ctor_get(v_r_2762_, 0);
lean_dec(v_unused_2816_);
v___x_2784_ = v_r_2762_;
v_isShared_2785_ = v_isSharedCheck_2811_;
goto v_resetjp_2783_;
}
else
{
lean_dec(v_r_2762_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2811_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___x_2799_; lean_object* v___y_2801_; 
v___x_2786_ = lean_nat_add(v___x_2756_, v_size_2758_);
lean_dec(v_size_2758_);
v___x_2787_ = lean_nat_add(v___x_2786_, v_size_2757_);
lean_dec(v___x_2786_);
v___x_2799_ = lean_nat_add(v___x_2756_, v_size_2774_);
if (lean_obj_tag(v_l_2778_) == 0)
{
lean_object* v_size_2809_; 
v_size_2809_ = lean_ctor_get(v_l_2778_, 0);
lean_inc(v_size_2809_);
v___y_2801_ = v_size_2809_;
goto v___jp_2800_;
}
else
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_unsigned_to_nat(0u);
v___y_2801_ = v___x_2810_;
goto v___jp_2800_;
}
v___jp_2788_:
{
lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2792_ = lean_nat_add(v___y_2789_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec(v___y_2789_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 4, v_impl_2755_);
lean_ctor_set(v___x_2784_, 3, v_r_2779_);
lean_ctor_set(v___x_2784_, 2, v_v_2263_);
lean_ctor_set(v___x_2784_, 1, v_k_2262_);
lean_ctor_set(v___x_2784_, 0, v___x_2792_);
v___x_2794_ = v___x_2784_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2798_, 3, v_r_2779_);
lean_ctor_set(v_reuseFailAlloc_2798_, 4, v_impl_2755_);
v___x_2794_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2796_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v___x_2794_);
lean_ctor_set(v___x_2772_, 3, v___y_2790_);
lean_ctor_set(v___x_2772_, 2, v_v_2777_);
lean_ctor_set(v___x_2772_, 1, v_k_2776_);
lean_ctor_set(v___x_2772_, 0, v___x_2787_);
v___x_2796_ = v___x_2772_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_k_2776_);
lean_ctor_set(v_reuseFailAlloc_2797_, 2, v_v_2777_);
lean_ctor_set(v_reuseFailAlloc_2797_, 3, v___y_2790_);
lean_ctor_set(v_reuseFailAlloc_2797_, 4, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
v___jp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2802_ = lean_nat_add(v___x_2799_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec(v___x_2799_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_l_2778_);
lean_ctor_set(v___x_2267_, 3, v_l_2761_);
lean_ctor_set(v___x_2267_, 2, v_v_2760_);
lean_ctor_set(v___x_2267_, 1, v_k_2759_);
lean_ctor_set(v___x_2267_, 0, v___x_2802_);
v___x_2804_ = v___x_2267_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v_k_2759_);
lean_ctor_set(v_reuseFailAlloc_2808_, 2, v_v_2760_);
lean_ctor_set(v_reuseFailAlloc_2808_, 3, v_l_2761_);
lean_ctor_set(v_reuseFailAlloc_2808_, 4, v_l_2778_);
v___x_2804_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_nat_add(v___x_2756_, v_size_2757_);
if (lean_obj_tag(v_r_2779_) == 0)
{
lean_object* v_size_2806_; 
v_size_2806_ = lean_ctor_get(v_r_2779_, 0);
lean_inc(v_size_2806_);
v___y_2789_ = v___x_2805_;
v___y_2790_ = v___x_2804_;
v___y_2791_ = v_size_2806_;
goto v___jp_2788_;
}
else
{
lean_object* v___x_2807_; 
v___x_2807_ = lean_unsigned_to_nat(0u);
v___y_2789_ = v___x_2805_;
v___y_2790_ = v___x_2804_;
v___y_2791_ = v___x_2807_;
goto v___jp_2788_;
}
}
}
}
}
else
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
lean_del_object(v___x_2267_);
v___x_2817_ = lean_nat_add(v___x_2756_, v_size_2758_);
lean_dec(v_size_2758_);
v___x_2818_ = lean_nat_add(v___x_2817_, v_size_2757_);
lean_dec(v___x_2817_);
v___x_2819_ = lean_nat_add(v___x_2756_, v_size_2757_);
v___x_2820_ = lean_nat_add(v___x_2819_, v_size_2775_);
lean_dec(v___x_2819_);
lean_inc_ref(v_impl_2755_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v_impl_2755_);
lean_ctor_set(v___x_2772_, 3, v_r_2762_);
lean_ctor_set(v___x_2772_, 2, v_v_2263_);
lean_ctor_set(v___x_2772_, 1, v_k_2262_);
lean_ctor_set(v___x_2772_, 0, v___x_2820_);
v___x_2822_ = v___x_2772_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2835_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2835_, 3, v_r_2762_);
lean_ctor_set(v_reuseFailAlloc_2835_, 4, v_impl_2755_);
v___x_2822_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
v_isSharedCheck_2829_ = !lean_is_exclusive(v_impl_2755_);
if (v_isSharedCheck_2829_ == 0)
{
lean_object* v_unused_2830_; lean_object* v_unused_2831_; lean_object* v_unused_2832_; lean_object* v_unused_2833_; lean_object* v_unused_2834_; 
v_unused_2830_ = lean_ctor_get(v_impl_2755_, 4);
lean_dec(v_unused_2830_);
v_unused_2831_ = lean_ctor_get(v_impl_2755_, 3);
lean_dec(v_unused_2831_);
v_unused_2832_ = lean_ctor_get(v_impl_2755_, 2);
lean_dec(v_unused_2832_);
v_unused_2833_ = lean_ctor_get(v_impl_2755_, 1);
lean_dec(v_unused_2833_);
v_unused_2834_ = lean_ctor_get(v_impl_2755_, 0);
lean_dec(v_unused_2834_);
v___x_2824_ = v_impl_2755_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_dec(v_impl_2755_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 4, v___x_2822_);
lean_ctor_set(v___x_2824_, 3, v_l_2761_);
lean_ctor_set(v___x_2824_, 2, v_v_2760_);
lean_ctor_set(v___x_2824_, 1, v_k_2759_);
lean_ctor_set(v___x_2824_, 0, v___x_2818_);
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_k_2759_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_v_2760_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_l_2761_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v___x_2822_);
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
}
}
}
else
{
lean_object* v_size_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v_size_2842_ = lean_ctor_get(v_impl_2755_, 0);
v___x_2843_ = lean_nat_add(v___x_2756_, v_size_2842_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_impl_2755_);
lean_ctor_set(v___x_2267_, 0, v___x_2843_);
v___x_2845_ = v___x_2267_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2846_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2846_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2846_, 4, v_impl_2755_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
else
{
if (lean_obj_tag(v_l_2264_) == 0)
{
lean_object* v_l_2847_; 
v_l_2847_ = lean_ctor_get(v_l_2264_, 3);
if (lean_obj_tag(v_l_2847_) == 0)
{
lean_object* v_r_2848_; 
lean_inc_ref(v_l_2847_);
v_r_2848_ = lean_ctor_get(v_l_2264_, 4);
lean_inc(v_r_2848_);
if (lean_obj_tag(v_r_2848_) == 0)
{
lean_object* v_size_2849_; lean_object* v_k_2850_; lean_object* v_v_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2864_; 
v_size_2849_ = lean_ctor_get(v_l_2264_, 0);
v_k_2850_ = lean_ctor_get(v_l_2264_, 1);
v_v_2851_ = lean_ctor_get(v_l_2264_, 2);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_l_2264_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; lean_object* v_unused_2866_; 
v_unused_2865_ = lean_ctor_get(v_l_2264_, 4);
lean_dec(v_unused_2865_);
v_unused_2866_ = lean_ctor_get(v_l_2264_, 3);
lean_dec(v_unused_2866_);
v___x_2853_ = v_l_2264_;
v_isShared_2854_ = v_isSharedCheck_2864_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_v_2851_);
lean_inc(v_k_2850_);
lean_inc(v_size_2849_);
lean_dec(v_l_2264_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2864_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v_size_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v_size_2855_ = lean_ctor_get(v_r_2848_, 0);
v___x_2856_ = lean_nat_add(v___x_2756_, v_size_2849_);
lean_dec(v_size_2849_);
v___x_2857_ = lean_nat_add(v___x_2756_, v_size_2855_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 4, v_impl_2755_);
lean_ctor_set(v___x_2853_, 3, v_r_2848_);
lean_ctor_set(v___x_2853_, 2, v_v_2263_);
lean_ctor_set(v___x_2853_, 1, v_k_2262_);
lean_ctor_set(v___x_2853_, 0, v___x_2857_);
v___x_2859_ = v___x_2853_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2863_, 3, v_r_2848_);
lean_ctor_set(v_reuseFailAlloc_2863_, 4, v_impl_2755_);
v___x_2859_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2861_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2859_);
lean_ctor_set(v___x_2267_, 3, v_l_2847_);
lean_ctor_set(v___x_2267_, 2, v_v_2851_);
lean_ctor_set(v___x_2267_, 1, v_k_2850_);
lean_ctor_set(v___x_2267_, 0, v___x_2856_);
v___x_2861_ = v___x_2267_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_k_2850_);
lean_ctor_set(v_reuseFailAlloc_2862_, 2, v_v_2851_);
lean_ctor_set(v_reuseFailAlloc_2862_, 3, v_l_2847_);
lean_ctor_set(v_reuseFailAlloc_2862_, 4, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v_k_2867_; lean_object* v_v_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2879_; 
v_k_2867_ = lean_ctor_get(v_l_2264_, 1);
v_v_2868_ = lean_ctor_get(v_l_2264_, 2);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_l_2264_);
if (v_isSharedCheck_2879_ == 0)
{
lean_object* v_unused_2880_; lean_object* v_unused_2881_; lean_object* v_unused_2882_; 
v_unused_2880_ = lean_ctor_get(v_l_2264_, 4);
lean_dec(v_unused_2880_);
v_unused_2881_ = lean_ctor_get(v_l_2264_, 3);
lean_dec(v_unused_2881_);
v_unused_2882_ = lean_ctor_get(v_l_2264_, 0);
lean_dec(v_unused_2882_);
v___x_2870_ = v_l_2264_;
v_isShared_2871_ = v_isSharedCheck_2879_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_v_2868_);
lean_inc(v_k_2867_);
lean_dec(v_l_2264_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2879_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2872_ = lean_unsigned_to_nat(3u);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 3, v_r_2848_);
lean_ctor_set(v___x_2870_, 2, v_v_2263_);
lean_ctor_set(v___x_2870_, 1, v_k_2262_);
lean_ctor_set(v___x_2870_, 0, v___x_2756_);
v___x_2874_ = v___x_2870_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2878_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2878_, 3, v_r_2848_);
lean_ctor_set(v_reuseFailAlloc_2878_, 4, v_r_2848_);
v___x_2874_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2874_);
lean_ctor_set(v___x_2267_, 3, v_l_2847_);
lean_ctor_set(v___x_2267_, 2, v_v_2868_);
lean_ctor_set(v___x_2267_, 1, v_k_2867_);
lean_ctor_set(v___x_2267_, 0, v___x_2872_);
v___x_2876_ = v___x_2267_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_k_2867_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_v_2868_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_l_2847_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
else
{
lean_object* v_r_2883_; 
v_r_2883_ = lean_ctor_get(v_l_2264_, 4);
lean_inc(v_r_2883_);
if (lean_obj_tag(v_r_2883_) == 0)
{
lean_object* v_k_2884_; lean_object* v_v_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2908_; 
lean_inc(v_l_2847_);
v_k_2884_ = lean_ctor_get(v_l_2264_, 1);
v_v_2885_ = lean_ctor_get(v_l_2264_, 2);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_l_2264_);
if (v_isSharedCheck_2908_ == 0)
{
lean_object* v_unused_2909_; lean_object* v_unused_2910_; lean_object* v_unused_2911_; 
v_unused_2909_ = lean_ctor_get(v_l_2264_, 4);
lean_dec(v_unused_2909_);
v_unused_2910_ = lean_ctor_get(v_l_2264_, 3);
lean_dec(v_unused_2910_);
v_unused_2911_ = lean_ctor_get(v_l_2264_, 0);
lean_dec(v_unused_2911_);
v___x_2887_ = v_l_2264_;
v_isShared_2888_ = v_isSharedCheck_2908_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_v_2885_);
lean_inc(v_k_2884_);
lean_dec(v_l_2264_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2908_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v_k_2889_; lean_object* v_v_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2904_; 
v_k_2889_ = lean_ctor_get(v_r_2883_, 1);
v_v_2890_ = lean_ctor_get(v_r_2883_, 2);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_r_2883_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; lean_object* v_unused_2906_; lean_object* v_unused_2907_; 
v_unused_2905_ = lean_ctor_get(v_r_2883_, 4);
lean_dec(v_unused_2905_);
v_unused_2906_ = lean_ctor_get(v_r_2883_, 3);
lean_dec(v_unused_2906_);
v_unused_2907_ = lean_ctor_get(v_r_2883_, 0);
lean_dec(v_unused_2907_);
v___x_2892_ = v_r_2883_;
v_isShared_2893_ = v_isSharedCheck_2904_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_v_2890_);
lean_inc(v_k_2889_);
lean_dec(v_r_2883_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2904_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2894_ = lean_unsigned_to_nat(3u);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 4, v_l_2847_);
lean_ctor_set(v___x_2892_, 3, v_l_2847_);
lean_ctor_set(v___x_2892_, 2, v_v_2885_);
lean_ctor_set(v___x_2892_, 1, v_k_2884_);
lean_ctor_set(v___x_2892_, 0, v___x_2756_);
v___x_2896_ = v___x_2892_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_k_2884_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_v_2885_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_l_2847_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_l_2847_);
v___x_2896_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2898_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 4, v_l_2847_);
lean_ctor_set(v___x_2887_, 2, v_v_2263_);
lean_ctor_set(v___x_2887_, 1, v_k_2262_);
lean_ctor_set(v___x_2887_, 0, v___x_2756_);
v___x_2898_ = v___x_2887_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2902_, 3, v_l_2847_);
lean_ctor_set(v_reuseFailAlloc_2902_, 4, v_l_2847_);
v___x_2898_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2900_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2898_);
lean_ctor_set(v___x_2267_, 3, v___x_2896_);
lean_ctor_set(v___x_2267_, 2, v_v_2890_);
lean_ctor_set(v___x_2267_, 1, v_k_2889_);
lean_ctor_set(v___x_2267_, 0, v___x_2894_);
v___x_2900_ = v___x_2267_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_k_2889_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_v_2890_);
lean_ctor_set(v_reuseFailAlloc_2901_, 3, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2901_, 4, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2912_ = lean_unsigned_to_nat(2u);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_r_2883_);
lean_ctor_set(v___x_2267_, 0, v___x_2912_);
v___x_2914_ = v___x_2267_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2915_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2915_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2915_, 4, v_r_2883_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
lean_object* v___x_2917_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_l_2264_);
lean_ctor_set(v___x_2267_, 0, v___x_2756_);
v___x_2917_ = v___x_2267_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2918_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_l_2264_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
}
}
else
{
return v_t_2261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_2921_, lean_object* v_t_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2921_, v_t_2922_);
lean_dec(v_k_2921_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_2924_, lean_object* v_declName_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v_ext_2931_; lean_object* v_toEnvExtension_2932_; lean_object* v_env_2933_; lean_object* v_asyncMode_2934_; uint8_t v___x_2935_; lean_object* v___x_2936_; lean_object* v_funCC_2937_; lean_object* v___y_2939_; uint8_t v___x_2965_; 
v___x_2929_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2930_ = lean_st_ref_get(v_a_2927_);
v_ext_2931_ = lean_ctor_get(v_ext_2924_, 1);
v_toEnvExtension_2932_ = lean_ctor_get(v_ext_2931_, 0);
v_env_2933_ = lean_ctor_get(v___x_2930_, 0);
lean_inc_ref(v_env_2933_);
lean_dec(v___x_2930_);
v_asyncMode_2934_ = lean_ctor_get(v_toEnvExtension_2932_, 2);
v___x_2935_ = 0;
v___x_2936_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2929_, v_ext_2924_, v_env_2933_, v_asyncMode_2934_, v___x_2935_);
v_funCC_2937_ = lean_ctor_get(v___x_2936_, 2);
lean_inc(v_funCC_2937_);
lean_dec(v___x_2936_);
v___x_2965_ = l_Lean_NameSet_contains(v_funCC_2937_, v_declName_2925_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; 
lean_inc(v_declName_2925_);
v___x_2966_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2925_, v_a_2926_, v_a_2927_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_dec_ref_known(v___x_2966_, 1);
v___y_2939_ = v_a_2927_;
goto v___jp_2938_;
}
else
{
lean_dec(v_funCC_2937_);
lean_dec(v_declName_2925_);
lean_dec_ref(v_ext_2924_);
return v___x_2966_;
}
}
else
{
v___y_2939_ = v_a_2927_;
goto v___jp_2938_;
}
v___jp_2938_:
{
lean_object* v___x_2940_; lean_object* v___f_2941_; lean_object* v___x_2942_; lean_object* v_env_2943_; lean_object* v_nextMacroScope_2944_; lean_object* v_ngen_2945_; lean_object* v_auxDeclNGen_2946_; lean_object* v_traceState_2947_; lean_object* v_recordedDeps_2948_; lean_object* v_messages_2949_; lean_object* v_infoState_2950_; lean_object* v_snapshotTasks_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2963_; 
v___x_2940_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_2925_, v_funCC_2937_);
lean_dec(v_declName_2925_);
v___f_2941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_2941_, 0, v___x_2940_);
v___x_2942_ = lean_st_ref_take(v___y_2939_);
v_env_2943_ = lean_ctor_get(v___x_2942_, 0);
v_nextMacroScope_2944_ = lean_ctor_get(v___x_2942_, 1);
v_ngen_2945_ = lean_ctor_get(v___x_2942_, 2);
v_auxDeclNGen_2946_ = lean_ctor_get(v___x_2942_, 3);
v_traceState_2947_ = lean_ctor_get(v___x_2942_, 4);
v_recordedDeps_2948_ = lean_ctor_get(v___x_2942_, 6);
v_messages_2949_ = lean_ctor_get(v___x_2942_, 7);
v_infoState_2950_ = lean_ctor_get(v___x_2942_, 8);
v_snapshotTasks_2951_ = lean_ctor_get(v___x_2942_, 9);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2963_ == 0)
{
lean_object* v_unused_2964_; 
v_unused_2964_ = lean_ctor_get(v___x_2942_, 5);
lean_dec(v_unused_2964_);
v___x_2953_ = v___x_2942_;
v_isShared_2954_ = v_isSharedCheck_2963_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_snapshotTasks_2951_);
lean_inc(v_infoState_2950_);
lean_inc(v_messages_2949_);
lean_inc(v_recordedDeps_2948_);
lean_inc(v_traceState_2947_);
lean_inc(v_auxDeclNGen_2946_);
lean_inc(v_ngen_2945_);
lean_inc(v_nextMacroScope_2944_);
lean_inc(v_env_2943_);
lean_dec(v___x_2942_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2963_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2955_ = lean_box(0);
v___x_2956_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2924_, v_env_2943_, v___f_2941_);
v___x_2957_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 5, v___x_2957_);
lean_ctor_set(v___x_2953_, 0, v___x_2956_);
v___x_2959_ = v___x_2953_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v_nextMacroScope_2944_);
lean_ctor_set(v_reuseFailAlloc_2962_, 2, v_ngen_2945_);
lean_ctor_set(v_reuseFailAlloc_2962_, 3, v_auxDeclNGen_2946_);
lean_ctor_set(v_reuseFailAlloc_2962_, 4, v_traceState_2947_);
lean_ctor_set(v_reuseFailAlloc_2962_, 5, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_2962_, 6, v_recordedDeps_2948_);
lean_ctor_set(v_reuseFailAlloc_2962_, 7, v_messages_2949_);
lean_ctor_set(v_reuseFailAlloc_2962_, 8, v_infoState_2950_);
lean_ctor_set(v_reuseFailAlloc_2962_, 9, v_snapshotTasks_2951_);
v___x_2959_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = lean_st_ref_put(v___y_2939_, v___x_2959_);
v___x_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2955_);
return v___x_2961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_2967_, lean_object* v_declName_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2967_, v_declName_2968_, v_a_2969_, v_a_2970_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_2973_, lean_object* v_k_2974_, lean_object* v_t_2975_, lean_object* v_h_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2974_, v_t_2975_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_2978_, lean_object* v_k_2979_, lean_object* v_t_2980_, lean_object* v_h_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_2978_, v_k_2979_, v_t_2980_, v_h_2981_);
lean_dec(v_k_2979_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_2983_, lean_object* v_s_2984_){
_start:
{
lean_object* v_casesTypes_2985_; lean_object* v_extThms_2986_; lean_object* v_funCC_2987_; lean_object* v_inj_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
v_casesTypes_2985_ = lean_ctor_get(v_s_2984_, 0);
v_extThms_2986_ = lean_ctor_get(v_s_2984_, 1);
v_funCC_2987_ = lean_ctor_get(v_s_2984_, 2);
v_inj_2988_ = lean_ctor_get(v_s_2984_, 4);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_s_2984_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; 
v_unused_2996_ = lean_ctor_get(v_s_2984_, 3);
lean_dec(v_unused_2996_);
v___x_2990_ = v_s_2984_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_inj_2988_);
lean_inc(v_funCC_2987_);
lean_inc(v_extThms_2986_);
lean_inc(v_casesTypes_2985_);
lean_dec(v_s_2984_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 3, v_a_2983_);
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_casesTypes_2985_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_extThms_2986_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_funCC_2987_);
lean_ctor_set(v_reuseFailAlloc_2994_, 3, v_a_2983_);
lean_ctor_set(v_reuseFailAlloc_2994_, 4, v_inj_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_2997_, lean_object* v_declName_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v_ext_3006_; lean_object* v_toEnvExtension_3007_; lean_object* v_env_3008_; lean_object* v_asyncMode_3009_; uint8_t v___x_3010_; lean_object* v___x_3011_; lean_object* v_ematch_3012_; lean_object* v___x_3013_; 
v___x_3004_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3005_ = lean_st_ref_get(v_a_3002_);
v_ext_3006_ = lean_ctor_get(v_ext_2997_, 1);
v_toEnvExtension_3007_ = lean_ctor_get(v_ext_3006_, 0);
v_env_3008_ = lean_ctor_get(v___x_3005_, 0);
lean_inc_ref(v_env_3008_);
lean_dec(v___x_3005_);
v_asyncMode_3009_ = lean_ctor_get(v_toEnvExtension_3007_, 2);
v___x_3010_ = 0;
v___x_3011_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3004_, v_ext_2997_, v_env_3008_, v_asyncMode_3009_, v___x_3010_);
v_ematch_3012_ = lean_ctor_get(v___x_3011_, 3);
lean_inc_ref(v_ematch_3012_);
lean_dec(v___x_3011_);
v___x_3013_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_3012_, v_declName_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3059_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3059_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3059_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___f_3018_; lean_object* v___x_3019_; lean_object* v_env_3020_; lean_object* v_nextMacroScope_3021_; lean_object* v_ngen_3022_; lean_object* v_auxDeclNGen_3023_; lean_object* v_traceState_3024_; lean_object* v_recordedDeps_3025_; lean_object* v_messages_3026_; lean_object* v_infoState_3027_; lean_object* v_snapshotTasks_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3057_; 
v___f_3018_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_3018_, 0, v_a_3014_);
v___x_3019_ = lean_st_ref_take(v_a_3002_);
v_env_3020_ = lean_ctor_get(v___x_3019_, 0);
v_nextMacroScope_3021_ = lean_ctor_get(v___x_3019_, 1);
v_ngen_3022_ = lean_ctor_get(v___x_3019_, 2);
v_auxDeclNGen_3023_ = lean_ctor_get(v___x_3019_, 3);
v_traceState_3024_ = lean_ctor_get(v___x_3019_, 4);
v_recordedDeps_3025_ = lean_ctor_get(v___x_3019_, 6);
v_messages_3026_ = lean_ctor_get(v___x_3019_, 7);
v_infoState_3027_ = lean_ctor_get(v___x_3019_, 8);
v_snapshotTasks_3028_ = lean_ctor_get(v___x_3019_, 9);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3057_ == 0)
{
lean_object* v_unused_3058_; 
v_unused_3058_ = lean_ctor_get(v___x_3019_, 5);
lean_dec(v_unused_3058_);
v___x_3030_ = v___x_3019_;
v_isShared_3031_ = v_isSharedCheck_3057_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_snapshotTasks_3028_);
lean_inc(v_infoState_3027_);
lean_inc(v_messages_3026_);
lean_inc(v_recordedDeps_3025_);
lean_inc(v_traceState_3024_);
lean_inc(v_auxDeclNGen_3023_);
lean_inc(v_ngen_3022_);
lean_inc(v_nextMacroScope_3021_);
lean_inc(v_env_3020_);
lean_dec(v___x_3019_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3057_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___x_3032_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2997_, v_env_3020_, v___f_3018_);
v___x_3033_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 5, v___x_3033_);
lean_ctor_set(v___x_3030_, 0, v___x_3032_);
v___x_3035_ = v___x_3030_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_nextMacroScope_3021_);
lean_ctor_set(v_reuseFailAlloc_3056_, 2, v_ngen_3022_);
lean_ctor_set(v_reuseFailAlloc_3056_, 3, v_auxDeclNGen_3023_);
lean_ctor_set(v_reuseFailAlloc_3056_, 4, v_traceState_3024_);
lean_ctor_set(v_reuseFailAlloc_3056_, 5, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3056_, 6, v_recordedDeps_3025_);
lean_ctor_set(v_reuseFailAlloc_3056_, 7, v_messages_3026_);
lean_ctor_set(v_reuseFailAlloc_3056_, 8, v_infoState_3027_);
lean_ctor_set(v_reuseFailAlloc_3056_, 9, v_snapshotTasks_3028_);
v___x_3035_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v_mctx_3038_; lean_object* v_zetaDeltaFVarIds_3039_; lean_object* v_postponed_3040_; lean_object* v_diag_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3054_; 
v___x_3036_ = lean_st_ref_put(v_a_3002_, v___x_3035_);
v___x_3037_ = lean_st_ref_take(v_a_3000_);
v_mctx_3038_ = lean_ctor_get(v___x_3037_, 0);
v_zetaDeltaFVarIds_3039_ = lean_ctor_get(v___x_3037_, 2);
v_postponed_3040_ = lean_ctor_get(v___x_3037_, 3);
v_diag_3041_ = lean_ctor_get(v___x_3037_, 4);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; 
v_unused_3055_ = lean_ctor_get(v___x_3037_, 1);
lean_dec(v_unused_3055_);
v___x_3043_ = v___x_3037_;
v_isShared_3044_ = v_isSharedCheck_3054_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_diag_3041_);
lean_inc(v_postponed_3040_);
lean_inc(v_zetaDeltaFVarIds_3039_);
lean_inc(v_mctx_3038_);
lean_dec(v___x_3037_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3054_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3045_ = lean_box(0);
v___x_3046_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 1, v___x_3046_);
v___x_3048_ = v___x_3043_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_mctx_3038_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3053_, 2, v_zetaDeltaFVarIds_3039_);
lean_ctor_set(v_reuseFailAlloc_3053_, 3, v_postponed_3040_);
lean_ctor_set(v_reuseFailAlloc_3053_, 4, v_diag_3041_);
v___x_3048_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3049_ = lean_st_ref_put(v_a_3000_, v___x_3048_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3045_);
v___x_3051_ = v___x_3016_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3045_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec_ref(v_ext_2997_);
v_a_3060_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3013_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3013_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_3068_, lean_object* v_declName_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_3068_, v_declName_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_3076_, lean_object* v_s_3077_){
_start:
{
lean_object* v_casesTypes_3078_; lean_object* v_extThms_3079_; lean_object* v_funCC_3080_; lean_object* v_ematch_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
v_casesTypes_3078_ = lean_ctor_get(v_s_3077_, 0);
v_extThms_3079_ = lean_ctor_get(v_s_3077_, 1);
v_funCC_3080_ = lean_ctor_get(v_s_3077_, 2);
v_ematch_3081_ = lean_ctor_get(v_s_3077_, 3);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_s_3077_);
if (v_isSharedCheck_3088_ == 0)
{
lean_object* v_unused_3089_; 
v_unused_3089_ = lean_ctor_get(v_s_3077_, 4);
lean_dec(v_unused_3089_);
v___x_3083_ = v_s_3077_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_ematch_3081_);
lean_inc(v_funCC_3080_);
lean_inc(v_extThms_3079_);
lean_inc(v_casesTypes_3078_);
lean_dec(v_s_3077_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 4, v_a_3076_);
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_casesTypes_3078_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_extThms_3079_);
lean_ctor_set(v_reuseFailAlloc_3087_, 2, v_funCC_3080_);
lean_ctor_set(v_reuseFailAlloc_3087_, 3, v_ematch_3081_);
lean_ctor_set(v_reuseFailAlloc_3087_, 4, v_a_3076_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_3090_, lean_object* v_declName_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v_ext_3099_; lean_object* v_toEnvExtension_3100_; lean_object* v_env_3101_; lean_object* v_asyncMode_3102_; uint8_t v___x_3103_; lean_object* v___x_3104_; lean_object* v_inj_3105_; lean_object* v___x_3106_; 
v___x_3097_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3098_ = lean_st_ref_get(v_a_3095_);
v_ext_3099_ = lean_ctor_get(v_ext_3090_, 1);
v_toEnvExtension_3100_ = lean_ctor_get(v_ext_3099_, 0);
v_env_3101_ = lean_ctor_get(v___x_3098_, 0);
lean_inc_ref(v_env_3101_);
lean_dec(v___x_3098_);
v_asyncMode_3102_ = lean_ctor_get(v_toEnvExtension_3100_, 2);
v___x_3103_ = 0;
v___x_3104_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3097_, v_ext_3090_, v_env_3101_, v_asyncMode_3102_, v___x_3103_);
v_inj_3105_ = lean_ctor_get(v___x_3104_, 4);
lean_inc_ref(v_inj_3105_);
lean_dec(v___x_3104_);
v___x_3106_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_3105_, v_declName_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3152_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3152_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3152_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___f_3111_; lean_object* v___x_3112_; lean_object* v_env_3113_; lean_object* v_nextMacroScope_3114_; lean_object* v_ngen_3115_; lean_object* v_auxDeclNGen_3116_; lean_object* v_traceState_3117_; lean_object* v_recordedDeps_3118_; lean_object* v_messages_3119_; lean_object* v_infoState_3120_; lean_object* v_snapshotTasks_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3150_; 
v___f_3111_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_3111_, 0, v_a_3107_);
v___x_3112_ = lean_st_ref_take(v_a_3095_);
v_env_3113_ = lean_ctor_get(v___x_3112_, 0);
v_nextMacroScope_3114_ = lean_ctor_get(v___x_3112_, 1);
v_ngen_3115_ = lean_ctor_get(v___x_3112_, 2);
v_auxDeclNGen_3116_ = lean_ctor_get(v___x_3112_, 3);
v_traceState_3117_ = lean_ctor_get(v___x_3112_, 4);
v_recordedDeps_3118_ = lean_ctor_get(v___x_3112_, 6);
v_messages_3119_ = lean_ctor_get(v___x_3112_, 7);
v_infoState_3120_ = lean_ctor_get(v___x_3112_, 8);
v_snapshotTasks_3121_ = lean_ctor_get(v___x_3112_, 9);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v___x_3112_, 5);
lean_dec(v_unused_3151_);
v___x_3123_ = v___x_3112_;
v_isShared_3124_ = v_isSharedCheck_3150_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_snapshotTasks_3121_);
lean_inc(v_infoState_3120_);
lean_inc(v_messages_3119_);
lean_inc(v_recordedDeps_3118_);
lean_inc(v_traceState_3117_);
lean_inc(v_auxDeclNGen_3116_);
lean_inc(v_ngen_3115_);
lean_inc(v_nextMacroScope_3114_);
lean_inc(v_env_3113_);
lean_dec(v___x_3112_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3150_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3125_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_3090_, v_env_3113_, v___f_3111_);
v___x_3126_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 5, v___x_3126_);
lean_ctor_set(v___x_3123_, 0, v___x_3125_);
v___x_3128_ = v___x_3123_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3125_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_nextMacroScope_3114_);
lean_ctor_set(v_reuseFailAlloc_3149_, 2, v_ngen_3115_);
lean_ctor_set(v_reuseFailAlloc_3149_, 3, v_auxDeclNGen_3116_);
lean_ctor_set(v_reuseFailAlloc_3149_, 4, v_traceState_3117_);
lean_ctor_set(v_reuseFailAlloc_3149_, 5, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3149_, 6, v_recordedDeps_3118_);
lean_ctor_set(v_reuseFailAlloc_3149_, 7, v_messages_3119_);
lean_ctor_set(v_reuseFailAlloc_3149_, 8, v_infoState_3120_);
lean_ctor_set(v_reuseFailAlloc_3149_, 9, v_snapshotTasks_3121_);
v___x_3128_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v_mctx_3131_; lean_object* v_zetaDeltaFVarIds_3132_; lean_object* v_postponed_3133_; lean_object* v_diag_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3147_; 
v___x_3129_ = lean_st_ref_put(v_a_3095_, v___x_3128_);
v___x_3130_ = lean_st_ref_take(v_a_3093_);
v_mctx_3131_ = lean_ctor_get(v___x_3130_, 0);
v_zetaDeltaFVarIds_3132_ = lean_ctor_get(v___x_3130_, 2);
v_postponed_3133_ = lean_ctor_get(v___x_3130_, 3);
v_diag_3134_ = lean_ctor_get(v___x_3130_, 4);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v___x_3130_, 1);
lean_dec(v_unused_3148_);
v___x_3136_ = v___x_3130_;
v_isShared_3137_ = v_isSharedCheck_3147_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_diag_3134_);
lean_inc(v_postponed_3133_);
lean_inc(v_zetaDeltaFVarIds_3132_);
lean_inc(v_mctx_3131_);
lean_dec(v___x_3130_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3147_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3138_ = lean_box(0);
v___x_3139_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 1, v___x_3139_);
v___x_3141_ = v___x_3136_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_mctx_3131_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v_zetaDeltaFVarIds_3132_);
lean_ctor_set(v_reuseFailAlloc_3146_, 3, v_postponed_3133_);
lean_ctor_set(v_reuseFailAlloc_3146_, 4, v_diag_3134_);
v___x_3141_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = lean_st_ref_put(v_a_3093_, v___x_3141_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3138_);
v___x_3144_ = v___x_3109_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3138_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec_ref(v_ext_3090_);
v_a_3153_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3106_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3106_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_3161_, lean_object* v_declName_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_3161_, v_declName_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_);
lean_dec(v_a_3166_);
lean_dec_ref(v_a_3165_);
lean_dec(v_a_3164_);
lean_dec_ref(v_a_3163_);
return v_res_3168_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3169_, lean_object* v_i_3170_, lean_object* v_k_3171_){
_start:
{
lean_object* v___x_3172_; uint8_t v___x_3173_; 
v___x_3172_ = lean_array_get_size(v_keys_3169_);
v___x_3173_ = lean_nat_dec_lt(v_i_3170_, v___x_3172_);
if (v___x_3173_ == 0)
{
lean_dec(v_i_3170_);
return v___x_3173_;
}
else
{
lean_object* v_k_x27_3174_; uint8_t v___x_3175_; 
v_k_x27_3174_ = lean_array_fget_borrowed(v_keys_3169_, v_i_3170_);
v___x_3175_ = lean_name_eq(v_k_3171_, v_k_x27_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_unsigned_to_nat(1u);
v___x_3177_ = lean_nat_add(v_i_3170_, v___x_3176_);
lean_dec(v_i_3170_);
v_i_3170_ = v___x_3177_;
goto _start;
}
else
{
lean_dec(v_i_3170_);
return v___x_3173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3179_, lean_object* v_i_3180_, lean_object* v_k_3181_){
_start:
{
uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_res_3182_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_3179_, v_i_3180_, v_k_3181_);
lean_dec(v_k_3181_);
lean_dec_ref(v_keys_3179_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_3184_, size_t v_x_3185_, lean_object* v_x_3186_){
_start:
{
if (lean_obj_tag(v_x_3184_) == 0)
{
lean_object* v_es_3187_; lean_object* v___x_3188_; size_t v___x_3189_; size_t v___x_3190_; lean_object* v_j_3191_; lean_object* v___x_3192_; 
v_es_3187_ = lean_ctor_get(v_x_3184_, 0);
v___x_3188_ = lean_box(2);
v___x_3189_ = ((size_t)31ULL);
v___x_3190_ = lean_usize_land(v_x_3185_, v___x_3189_);
v_j_3191_ = lean_usize_to_nat(v___x_3190_);
v___x_3192_ = lean_array_get_borrowed(v___x_3188_, v_es_3187_, v_j_3191_);
lean_dec(v_j_3191_);
switch(lean_obj_tag(v___x_3192_))
{
case 0:
{
lean_object* v_key_3193_; uint8_t v___x_3194_; 
v_key_3193_ = lean_ctor_get(v___x_3192_, 0);
v___x_3194_ = lean_name_eq(v_x_3186_, v_key_3193_);
return v___x_3194_;
}
case 1:
{
lean_object* v_node_3195_; size_t v___x_3196_; size_t v___x_3197_; 
v_node_3195_ = lean_ctor_get(v___x_3192_, 0);
v___x_3196_ = ((size_t)5ULL);
v___x_3197_ = lean_usize_shift_right(v_x_3185_, v___x_3196_);
v_x_3184_ = v_node_3195_;
v_x_3185_ = v___x_3197_;
goto _start;
}
default: 
{
uint8_t v___x_3199_; 
v___x_3199_ = 0;
return v___x_3199_;
}
}
}
else
{
lean_object* v_ks_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v_ks_3200_ = lean_ctor_get(v_x_3184_, 0);
v___x_3201_ = lean_unsigned_to_nat(0u);
v___x_3202_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_3200_, v___x_3201_, v_x_3186_);
return v___x_3202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_3203_, lean_object* v_x_3204_, lean_object* v_x_3205_){
_start:
{
size_t v_x_330__boxed_3206_; uint8_t v_res_3207_; lean_object* v_r_3208_; 
v_x_330__boxed_3206_ = lean_unbox_usize(v_x_3204_);
lean_dec(v_x_3204_);
v_res_3207_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3203_, v_x_330__boxed_3206_, v_x_3205_);
lean_dec(v_x_3205_);
lean_dec_ref(v_x_3203_);
v_r_3208_ = lean_box(v_res_3207_);
return v_r_3208_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_3209_, lean_object* v_x_3210_){
_start:
{
uint64_t v___y_3212_; 
if (lean_obj_tag(v_x_3210_) == 0)
{
uint64_t v___x_3215_; 
v___x_3215_ = 1723ULL;
v___y_3212_ = v___x_3215_;
goto v___jp_3211_;
}
else
{
uint64_t v_hash_3216_; 
v_hash_3216_ = lean_ctor_get_uint64(v_x_3210_, sizeof(void*)*2);
v___y_3212_ = v_hash_3216_;
goto v___jp_3211_;
}
v___jp_3211_:
{
size_t v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = lean_uint64_to_usize(v___y_3212_);
v___x_3214_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3209_, v___x_3213_, v_x_3210_);
return v___x_3214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
uint8_t v_res_3219_; lean_object* v_r_3220_; 
v_res_3219_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_3217_, v_x_3218_);
lean_dec(v_x_3218_);
lean_dec_ref(v_x_3217_);
v_r_3220_ = lean_box(v_res_3219_);
return v_r_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_3221_, lean_object* v_declName_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v_ext_3227_; lean_object* v_toEnvExtension_3228_; lean_object* v_env_3229_; lean_object* v_asyncMode_3230_; uint8_t v___x_3231_; lean_object* v___x_3232_; lean_object* v_extThms_3233_; uint8_t v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3225_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3226_ = lean_st_ref_get(v_a_3223_);
v_ext_3227_ = lean_ctor_get(v_ext_3221_, 1);
v_toEnvExtension_3228_ = lean_ctor_get(v_ext_3227_, 0);
v_env_3229_ = lean_ctor_get(v___x_3226_, 0);
lean_inc_ref(v_env_3229_);
lean_dec(v___x_3226_);
v_asyncMode_3230_ = lean_ctor_get(v_toEnvExtension_3228_, 2);
v___x_3231_ = 0;
v___x_3232_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3225_, v_ext_3221_, v_env_3229_, v_asyncMode_3230_, v___x_3231_);
v_extThms_3233_ = lean_ctor_get(v___x_3232_, 1);
lean_inc_ref(v_extThms_3233_);
lean_dec(v___x_3232_);
v___x_3234_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_3233_, v_declName_3222_);
lean_dec_ref(v_extThms_3233_);
v___x_3235_ = lean_box(v___x_3234_);
v___x_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_3237_, lean_object* v_declName_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3237_, v_declName_3238_, v_a_3239_);
lean_dec(v_a_3239_);
lean_dec(v_declName_3238_);
lean_dec_ref(v_ext_3237_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_3242_, lean_object* v_declName_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3242_, v_declName_3243_, v_a_3245_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_3248_, lean_object* v_declName_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_3248_, v_declName_3249_, v_a_3250_, v_a_3251_);
lean_dec(v_a_3251_);
lean_dec_ref(v_a_3250_);
lean_dec(v_declName_3249_);
lean_dec_ref(v_ext_3248_);
return v_res_3253_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_3254_, lean_object* v_x_3255_, lean_object* v_x_3256_){
_start:
{
uint8_t v___x_3257_; 
v___x_3257_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_3255_, v_x_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_3258_, lean_object* v_x_3259_, lean_object* v_x_3260_){
_start:
{
uint8_t v_res_3261_; lean_object* v_r_3262_; 
v_res_3261_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_3258_, v_x_3259_, v_x_3260_);
lean_dec(v_x_3260_);
lean_dec_ref(v_x_3259_);
v_r_3262_ = lean_box(v_res_3261_);
return v_r_3262_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_3263_, lean_object* v_x_3264_, size_t v_x_3265_, lean_object* v_x_3266_){
_start:
{
uint8_t v___x_3267_; 
v___x_3267_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3264_, v_x_3265_, v_x_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_){
_start:
{
size_t v_x_417__boxed_3272_; uint8_t v_res_3273_; lean_object* v_r_3274_; 
v_x_417__boxed_3272_ = lean_unbox_usize(v_x_3270_);
lean_dec(v_x_3270_);
v_res_3273_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_3268_, v_x_3269_, v_x_417__boxed_3272_, v_x_3271_);
lean_dec(v_x_3271_);
lean_dec_ref(v_x_3269_);
v_r_3274_ = lean_box(v_res_3273_);
return v_r_3274_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3275_, lean_object* v_keys_3276_, lean_object* v_vals_3277_, lean_object* v_heq_3278_, lean_object* v_i_3279_, lean_object* v_k_3280_){
_start:
{
uint8_t v___x_3281_; 
v___x_3281_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_3276_, v_i_3279_, v_k_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3282_, lean_object* v_keys_3283_, lean_object* v_vals_3284_, lean_object* v_heq_3285_, lean_object* v_i_3286_, lean_object* v_k_3287_){
_start:
{
uint8_t v_res_3288_; lean_object* v_r_3289_; 
v_res_3288_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_3282_, v_keys_3283_, v_vals_3284_, v_heq_3285_, v_i_3286_, v_k_3287_);
lean_dec(v_k_3287_);
lean_dec_ref(v_vals_3284_);
lean_dec_ref(v_keys_3283_);
v_r_3289_ = lean_box(v_res_3288_);
return v_r_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_3290_, lean_object* v_declName_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v_ext_3296_; lean_object* v_toEnvExtension_3297_; lean_object* v_env_3298_; lean_object* v_asyncMode_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; lean_object* v_inj_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3294_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3295_ = lean_st_ref_get(v_a_3292_);
v_ext_3296_ = lean_ctor_get(v_ext_3290_, 1);
v_toEnvExtension_3297_ = lean_ctor_get(v_ext_3296_, 0);
v_env_3298_ = lean_ctor_get(v___x_3295_, 0);
lean_inc_ref(v_env_3298_);
lean_dec(v___x_3295_);
v_asyncMode_3299_ = lean_ctor_get(v_toEnvExtension_3297_, 2);
v___x_3300_ = 0;
v___x_3301_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3294_, v_ext_3290_, v_env_3298_, v_asyncMode_3299_, v___x_3300_);
v_inj_3302_ = lean_ctor_get(v___x_3301_, 4);
lean_inc_ref(v_inj_3302_);
lean_dec(v___x_3301_);
v___x_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3303_, 0, v_declName_3291_);
v___x_3304_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_3302_, v___x_3303_);
lean_dec_ref_known(v___x_3303_, 1);
lean_dec_ref(v_inj_3302_);
v___x_3305_ = lean_box(v___x_3304_);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_3307_, lean_object* v_declName_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3307_, v_declName_3308_, v_a_3309_);
lean_dec(v_a_3309_);
lean_dec_ref(v_ext_3307_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_3312_, lean_object* v_declName_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3312_, v_declName_3313_, v_a_3315_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_3318_, lean_object* v_declName_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_3318_, v_declName_3319_, v_a_3320_, v_a_3321_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
lean_dec_ref(v_ext_3318_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_3324_, lean_object* v_declName_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v_ext_3330_; lean_object* v_toEnvExtension_3331_; lean_object* v_env_3332_; lean_object* v_asyncMode_3333_; uint8_t v___x_3334_; lean_object* v___x_3335_; lean_object* v_funCC_3336_; uint8_t v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3328_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3329_ = lean_st_ref_get(v_a_3326_);
v_ext_3330_ = lean_ctor_get(v_ext_3324_, 1);
v_toEnvExtension_3331_ = lean_ctor_get(v_ext_3330_, 0);
v_env_3332_ = lean_ctor_get(v___x_3329_, 0);
lean_inc_ref(v_env_3332_);
lean_dec(v___x_3329_);
v_asyncMode_3333_ = lean_ctor_get(v_toEnvExtension_3331_, 2);
v___x_3334_ = 0;
v___x_3335_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3328_, v_ext_3324_, v_env_3332_, v_asyncMode_3333_, v___x_3334_);
v_funCC_3336_ = lean_ctor_get(v___x_3335_, 2);
lean_inc(v_funCC_3336_);
lean_dec(v___x_3335_);
v___x_3337_ = l_Lean_NameSet_contains(v_funCC_3336_, v_declName_3325_);
lean_dec(v_funCC_3336_);
v___x_3338_ = lean_box(v___x_3337_);
v___x_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_3340_, lean_object* v_declName_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3340_, v_declName_3341_, v_a_3342_);
lean_dec(v_a_3342_);
lean_dec(v_declName_3341_);
lean_dec_ref(v_ext_3340_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_3345_, lean_object* v_declName_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3345_, v_declName_3346_, v_a_3348_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_3351_, lean_object* v_declName_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_3351_, v_declName_3352_, v_a_3353_, v_a_3354_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_declName_3352_);
lean_dec_ref(v_ext_3351_);
return v_res_3356_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_3381_ = l_Lean_mkAtom(v___x_3380_);
return v___x_3381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3382_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_3383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3384_ = lean_array_push(v___x_3383_, v___x_3382_);
return v___x_3384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_3394_ = l_Lean_mkAtom(v___x_3393_);
return v___x_3394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3395_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_3396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3397_ = lean_array_push(v___x_3396_, v___x_3395_);
return v___x_3397_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3398_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_3399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_3400_ = lean_box(2);
v___x_3401_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
lean_ctor_set(v___x_3401_, 1, v___x_3399_);
lean_ctor_set(v___x_3401_, 2, v___x_3398_);
return v___x_3401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_3403_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_3404_ = lean_array_push(v___x_3403_, v___x_3402_);
return v___x_3404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_3406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_3407_ = lean_box(2);
v___x_3408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v___x_3406_);
lean_ctor_set(v___x_3408_, 2, v___x_3405_);
return v___x_3408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_3410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3411_ = lean_array_push(v___x_3410_, v___x_3409_);
return v___x_3411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_3413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_3414_ = lean_box(2);
v___x_3415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
lean_ctor_set(v___x_3415_, 1, v___x_3413_);
lean_ctor_set(v___x_3415_, 2, v___x_3412_);
return v___x_3415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_3417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3418_ = lean_array_push(v___x_3417_, v___x_3416_);
return v___x_3418_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3419_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_3420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_3421_ = lean_box(2);
v___x_3422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v___x_3420_);
lean_ctor_set(v___x_3422_, 2, v___x_3419_);
return v___x_3422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3423_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_3424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3425_ = lean_array_push(v___x_3424_, v___x_3423_);
return v___x_3425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3426_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_3427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_3428_ = lean_box(2);
v___x_3429_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
lean_ctor_set(v___x_3429_, 1, v___x_3427_);
lean_ctor_set(v___x_3429_, 2, v___x_3426_);
return v___x_3429_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_3431_, lean_object* v_ext_3432_, lean_object* v_____r_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
uint8_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = 0;
lean_inc(v_declName_3431_);
v___x_3440_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_3431_, v___x_3439_, v___y_3436_, v___y_3437_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; uint8_t v___x_3442_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3440_, 1);
v___x_3442_ = lean_unbox(v_a_3441_);
lean_dec(v_a_3441_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; lean_object* v_a_3444_; uint8_t v___x_3445_; 
v___x_3443_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3432_, v_declName_3431_, v___y_3437_);
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref(v___x_3443_);
v___x_3445_ = lean_unbox(v_a_3444_);
lean_dec(v_a_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; lean_object* v_a_3447_; uint8_t v___x_3448_; 
lean_inc(v_declName_3431_);
v___x_3446_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3432_, v_declName_3431_, v___y_3437_);
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref(v___x_3446_);
v___x_3448_ = lean_unbox(v_a_3447_);
lean_dec(v_a_3447_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3449_; lean_object* v_a_3450_; uint8_t v___x_3451_; 
v___x_3449_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3432_, v_declName_3431_, v___y_3437_);
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref(v___x_3449_);
v___x_3451_ = lean_unbox(v_a_3450_);
lean_dec(v_a_3450_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
v___x_3452_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_3432_, v_declName_3431_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
return v___x_3452_;
}
else
{
lean_object* v___x_3453_; 
v___x_3453_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_3432_, v_declName_3431_, v___y_3436_, v___y_3437_);
return v___x_3453_;
}
}
else
{
lean_object* v___x_3454_; 
v___x_3454_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_3432_, v_declName_3431_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
return v___x_3454_;
}
}
else
{
lean_object* v___x_3455_; 
v___x_3455_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_3432_, v_declName_3431_, v___y_3436_, v___y_3437_);
return v___x_3455_;
}
}
else
{
lean_object* v___x_3456_; 
v___x_3456_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_3432_, v_declName_3431_, v___y_3436_, v___y_3437_);
return v___x_3456_;
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec_ref(v_ext_3432_);
lean_dec(v_declName_3431_);
v_a_3457_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3440_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3440_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_3465_, lean_object* v_ext_3466_, lean_object* v_____r_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_3465_, v_ext_3466_, v_____r_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v_ref_3480_; lean_object* v___x_3481_; lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3490_; 
v_ref_3480_ = lean_ctor_get(v___y_3477_, 2);
v___x_3481_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msg_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3490_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3490_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
lean_inc(v_ref_3480_);
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v_ref_3480_);
lean_ctor_set(v___x_3486_, 1, v_a_3482_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set_tag(v___x_3484_, 1);
lean_ctor_set(v___x_3484_, 0, v___x_3486_);
v___x_3488_ = v___x_3484_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
return v_res_3497_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3504_; uint64_t v___x_3505_; 
v___x_3504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_3505_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3504_);
return v___x_3505_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_3507_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_3508_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
lean_ctor_set_uint64(v___x_3508_, sizeof(void*)*1, v___x_3506_);
return v___x_3508_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
return v___x_3510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3511_ = lean_box(1);
v___x_3512_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_3513_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
lean_ctor_set(v___x_3514_, 1, v___x_3512_);
lean_ctor_set(v___x_3514_, 2, v___x_3511_);
return v___x_3514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3517_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3518_ = lean_unsigned_to_nat(0u);
v___x_3519_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
lean_ctor_set(v___x_3519_, 2, v___x_3518_);
lean_ctor_set(v___x_3519_, 3, v___x_3518_);
lean_ctor_set(v___x_3519_, 4, v___x_3517_);
lean_ctor_set(v___x_3519_, 5, v___x_3517_);
lean_ctor_set(v___x_3519_, 6, v___x_3517_);
lean_ctor_set(v___x_3519_, 7, v___x_3517_);
lean_ctor_set(v___x_3519_, 8, v___x_3517_);
lean_ctor_set(v___x_3519_, 9, v___x_3517_);
lean_ctor_set(v___x_3519_, 10, v___x_3517_);
return v___x_3519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
return v___x_3521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3522_ = lean_unsigned_to_nat(0u);
v___x_3523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
lean_ctor_set(v___x_3524_, 2, v___x_3522_);
return v___x_3524_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3528_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
v___x_3529_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v___x_3527_);
lean_ctor_set(v___x_3529_, 2, v___x_3526_);
lean_ctor_set(v___x_3529_, 3, v___x_3527_);
lean_ctor_set(v___x_3529_, 4, v___x_3527_);
lean_ctor_set(v___x_3529_, 5, v___x_3527_);
lean_ctor_set(v___x_3529_, 6, v___x_3527_);
lean_ctor_set(v___x_3529_, 7, v___x_3525_);
return v___x_3529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10(void){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
lean_ctor_set(v___x_3531_, 2, v___x_3530_);
lean_ctor_set(v___x_3531_, 3, v___x_3530_);
lean_ctor_set(v___x_3531_, 4, v___x_3530_);
return v___x_3531_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11));
v___x_3534_ = l_Lean_stringToMessageData(v___x_3533_);
return v___x_3534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13));
v___x_3537_ = l_Lean_stringToMessageData(v___x_3536_);
return v___x_3537_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15));
v___x_3540_ = l_Lean_stringToMessageData(v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v_ext_3541_, lean_object* v___x_3542_, uint8_t v_showInfo_3543_, lean_object* v_attrName_3544_, lean_object* v_declName_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
uint8_t v___x_3549_; uint8_t v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___y_3564_; 
v___x_3549_ = 1;
v___x_3550_ = 0;
v___x_3551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3552_ = lean_unsigned_to_nat(0u);
v___x_3553_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_3554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_3555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_3556_ = lean_box(0);
lean_inc(v___x_3542_);
v___x_3557_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3557_, 0, v___x_3551_);
lean_ctor_set(v___x_3557_, 1, v___x_3542_);
lean_ctor_set(v___x_3557_, 2, v___x_3554_);
lean_ctor_set(v___x_3557_, 3, v___x_3555_);
lean_ctor_set(v___x_3557_, 4, v___x_3556_);
lean_ctor_set(v___x_3557_, 5, v___x_3552_);
lean_ctor_set(v___x_3557_, 6, v___x_3556_);
lean_ctor_set_uint8(v___x_3557_, sizeof(void*)*7, v___x_3550_);
lean_ctor_set_uint8(v___x_3557_, sizeof(void*)*7 + 1, v___x_3550_);
lean_ctor_set_uint8(v___x_3557_, sizeof(void*)*7 + 2, v___x_3550_);
lean_ctor_set_uint8(v___x_3557_, sizeof(void*)*7 + 3, v___x_3549_);
v___x_3558_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_3559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_3560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_3561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3558_);
lean_ctor_set(v___x_3561_, 1, v___x_3559_);
lean_ctor_set(v___x_3561_, 2, v___x_3542_);
lean_ctor_set(v___x_3561_, 3, v___x_3553_);
lean_ctor_set(v___x_3561_, 4, v___x_3560_);
v___x_3562_ = lean_st_mk_ref(v___x_3561_);
if (v_showInfo_3543_ == 0)
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_dec(v_attrName_3544_);
v___x_3574_ = lean_box(0);
v___x_3575_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_3545_, v_ext_3541_, v___x_3574_, v___x_3557_, v___x_3562_, v___y_3546_, v___y_3547_);
lean_dec_ref_known(v___x_3557_, 7);
v___y_3564_ = v___x_3575_;
goto v___jp_3563_;
}
else
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_dec(v_declName_3545_);
lean_dec_ref(v_ext_3541_);
v___x_3576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12);
v___x_3577_ = l_Lean_MessageData_ofName(v_attrName_3544_);
lean_inc_ref(v___x_3577_);
v___x_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3576_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14);
v___x_3580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3578_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___x_3581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
lean_ctor_set(v___x_3581_, 1, v___x_3577_);
v___x_3582_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16);
v___x_3583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3581_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3583_, v___x_3557_, v___x_3562_, v___y_3546_, v___y_3547_);
lean_dec(v___x_3562_);
lean_dec_ref_known(v___x_3557_, 7);
return v___x_3584_;
}
v___jp_3563_:
{
if (lean_obj_tag(v___y_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3573_; 
v_a_3565_ = lean_ctor_get(v___y_3564_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___y_3564_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3567_ = v___y_3564_;
v_isShared_3568_ = v_isSharedCheck_3573_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___y_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3573_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3571_; 
v___x_3569_ = lean_st_ref_get(v___x_3562_);
lean_dec(v___x_3562_);
lean_dec(v___x_3569_);
if (v_isShared_3568_ == 0)
{
v___x_3571_ = v___x_3567_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3565_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
else
{
lean_dec(v___x_3562_);
return v___y_3564_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v_ext_3585_, lean_object* v___x_3586_, lean_object* v_showInfo_3587_, lean_object* v_attrName_3588_, lean_object* v_declName_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
uint8_t v_showInfo_boxed_3593_; lean_object* v_res_3594_; 
v_showInfo_boxed_3593_ = lean_unbox(v_showInfo_3587_);
v_res_3594_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v_ext_3585_, v___x_3586_, v_showInfo_boxed_3593_, v_attrName_3588_, v_declName_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_3597_, uint8_t v_attrKind_3598_, uint8_t v_showInfo_3599_, uint8_t v_minIndexable_3600_, lean_object* v_as_x27_3601_, lean_object* v_b_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
if (lean_obj_tag(v_as_x27_3601_) == 0)
{
lean_object* v___x_3608_; 
lean_dec_ref(v_ext_3597_);
v___x_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3608_, 0, v_b_3602_);
return v___x_3608_;
}
else
{
lean_object* v_head_3609_; lean_object* v_tail_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v_head_3609_ = lean_ctor_get(v_as_x27_3601_, 0);
v_tail_3610_ = lean_ctor_get(v_as_x27_3601_, 1);
v___x_3611_ = lean_box(0);
v___x_3612_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3606_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
v___x_3614_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_3609_);
lean_inc_ref(v_ext_3597_);
v___x_3615_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_3597_, v_head_3609_, v_attrKind_3598_, v___x_3614_, v_a_3613_, v_showInfo_3599_, v_minIndexable_3600_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_dec_ref_known(v___x_3615_, 1);
v_as_x27_3601_ = v_tail_3610_;
v_b_3602_ = v___x_3611_;
goto _start;
}
else
{
lean_dec_ref(v_ext_3597_);
return v___x_3615_;
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec_ref(v_ext_3597_);
v_a_3617_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3612_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3612_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_3625_, lean_object* v_attrKind_3626_, lean_object* v_showInfo_3627_, lean_object* v_minIndexable_3628_, lean_object* v_as_x27_3629_, lean_object* v_b_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
uint8_t v_attrKind_boxed_3636_; uint8_t v_showInfo_boxed_3637_; uint8_t v_minIndexable_boxed_3638_; lean_object* v_res_3639_; 
v_attrKind_boxed_3636_ = lean_unbox(v_attrKind_3626_);
v_showInfo_boxed_3637_ = lean_unbox(v_showInfo_3627_);
v_minIndexable_boxed_3638_ = lean_unbox(v_minIndexable_3628_);
v_res_3639_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3625_, v_attrKind_boxed_3636_, v_showInfo_boxed_3637_, v_minIndexable_boxed_3638_, v_as_x27_3629_, v_b_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v_as_x27_3629_);
return v_res_3639_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_3642_ = l_Lean_stringToMessageData(v___x_3641_);
return v___x_3642_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_3645_ = l_Lean_stringToMessageData(v___x_3644_);
return v___x_3645_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_3648_ = l_Lean_stringToMessageData(v___x_3647_);
return v___x_3648_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_3651_ = l_Lean_stringToMessageData(v___x_3650_);
return v___x_3651_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_3656_ = l_Lean_stringToMessageData(v___x_3655_);
return v___x_3656_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_3659_ = l_Lean_stringToMessageData(v___x_3658_);
return v___x_3659_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14(void){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13));
v___x_3662_ = l_Lean_stringToMessageData(v___x_3661_);
return v___x_3662_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16(void){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15));
v___x_3665_ = l_Lean_stringToMessageData(v___x_3664_);
return v___x_3665_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18(void){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17));
v___x_3668_ = l_Lean_stringToMessageData(v___x_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_declName_3669_, uint8_t v_attrKind_3670_, lean_object* v_stx_3671_, lean_object* v_ext_3672_, uint8_t v_showInfo_3673_, uint8_t v_minIndexable_3674_, uint8_t v___x_3675_, lean_object* v_attrName_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_3671_, v___y_3679_, v___y_3680_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
switch(lean_obj_tag(v_a_3705_))
{
case 0:
{
lean_object* v_k_3706_; 
lean_dec(v_attrName_3676_);
lean_dec(v_stx_3671_);
v_k_3706_ = lean_ctor_get(v_a_3705_, 0);
lean_inc(v_k_3706_);
lean_dec_ref_known(v_a_3705_, 1);
if (lean_obj_tag(v_k_3706_) == 9)
{
lean_object* v___x_3707_; 
lean_dec_ref(v_ext_3672_);
lean_dec(v_declName_3669_);
v___x_3707_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_3679_, v___y_3680_);
return v___x_3707_;
}
else
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3680_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3710_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
v___x_3710_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_3672_, v_declName_3669_, v_attrKind_3670_, v_k_3706_, v_a_3709_, v_showInfo_3673_, v_minIndexable_3674_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3710_;
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v_k_3706_);
lean_dec_ref(v_ext_3672_);
lean_dec(v_declName_3669_);
v_a_3711_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3708_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3708_);
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
case 1:
{
uint8_t v_eager_3719_; lean_object* v___x_3720_; 
lean_dec(v_attrName_3676_);
lean_dec(v_stx_3671_);
v_eager_3719_ = lean_ctor_get_uint8(v_a_3705_, 0);
lean_dec_ref_known(v_a_3705_, 0);
v___x_3720_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_3672_, v_declName_3669_, v_eager_3719_, v_attrKind_3670_, v___y_3679_, v___y_3680_);
return v___x_3720_;
}
case 2:
{
lean_object* v___x_3721_; 
lean_dec(v_stx_3671_);
lean_inc(v_declName_3669_);
v___x_3721_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_3669_, v___x_3675_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3721_, 1);
if (lean_obj_tag(v_a_3722_) == 1)
{
lean_object* v_val_3723_; lean_object* v_ctors_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_dec(v_attrName_3676_);
lean_dec(v_declName_3669_);
v_val_3723_ = lean_ctor_get(v_a_3722_, 0);
lean_inc(v_val_3723_);
lean_dec_ref_known(v_a_3722_, 1);
v_ctors_3724_ = lean_ctor_get(v_val_3723_, 4);
lean_inc(v_ctors_3724_);
lean_dec(v_val_3723_);
v___x_3725_ = lean_box(0);
v___x_3726_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3672_, v_attrKind_3670_, v_showInfo_3673_, v_minIndexable_3674_, v_ctors_3724_, v___x_3725_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec(v_ctors_3724_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3733_ == 0)
{
lean_object* v_unused_3734_; 
v_unused_3734_ = lean_ctor_get(v___x_3726_, 0);
lean_dec(v_unused_3734_);
v___x_3728_ = v___x_3726_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_dec(v___x_3726_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 0, v___x_3725_);
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3725_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
else
{
return v___x_3726_;
}
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
lean_dec(v_a_3722_);
lean_dec_ref(v_ext_3672_);
v___x_3735_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_3736_ = l_Lean_MessageData_ofName(v_attrName_3676_);
v___x_3737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3735_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_3739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = l_Lean_MessageData_ofConstName(v_declName_3669_, v___x_3675_);
v___x_3741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_3743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3741_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___x_3744_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3743_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3744_;
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec(v_attrName_3676_);
lean_dec_ref(v_ext_3672_);
lean_dec(v_declName_3669_);
v_a_3745_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3721_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3721_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
case 3:
{
lean_object* v___x_3753_; 
lean_dec(v_attrName_3676_);
lean_inc(v_declName_3669_);
v___x_3753_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_3669_, v___x_3675_, v___y_3679_, v___y_3680_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v_a_3754_; 
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3753_, 1);
if (lean_obj_tag(v_a_3754_) == 1)
{
lean_object* v_val_3755_; lean_object* v___x_3756_; 
lean_dec(v_stx_3671_);
lean_dec(v_declName_3669_);
v_val_3755_ = lean_ctor_get(v_a_3754_, 0);
lean_inc_n(v_val_3755_, 2);
lean_dec_ref_known(v_a_3754_, 1);
lean_inc_ref(v_ext_3672_);
v___x_3756_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_3672_, v_val_3755_, v___x_3675_, v_attrKind_3670_, v___y_3679_, v___y_3680_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v___x_3757_; 
lean_dec_ref_known(v___x_3756_, 1);
v___x_3757_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3755_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3778_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3760_ = v___x_3757_;
v_isShared_3761_ = v_isSharedCheck_3778_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3757_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3778_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
if (lean_obj_tag(v_a_3758_) == 1)
{
lean_object* v_val_3762_; lean_object* v_ctors_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
lean_del_object(v___x_3760_);
v_val_3762_ = lean_ctor_get(v_a_3758_, 0);
lean_inc(v_val_3762_);
lean_dec_ref_known(v_a_3758_, 1);
v_ctors_3763_ = lean_ctor_get(v_val_3762_, 4);
lean_inc(v_ctors_3763_);
lean_dec(v_val_3762_);
v___x_3764_ = lean_box(0);
v___x_3765_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3672_, v_attrKind_3670_, v_showInfo_3673_, v_minIndexable_3674_, v_ctors_3763_, v___x_3764_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec(v_ctors_3763_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3772_ == 0)
{
lean_object* v_unused_3773_; 
v_unused_3773_ = lean_ctor_get(v___x_3765_, 0);
lean_dec(v_unused_3773_);
v___x_3767_ = v___x_3765_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_dec(v___x_3765_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 0, v___x_3764_);
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3764_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
else
{
return v___x_3765_;
}
}
else
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
lean_dec(v_a_3758_);
lean_dec_ref(v_ext_3672_);
v___x_3774_ = lean_box(0);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 0, v___x_3774_);
v___x_3776_ = v___x_3760_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec_ref(v_ext_3672_);
v_a_3779_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3757_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3757_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
else
{
lean_dec(v_val_3755_);
lean_dec_ref(v_ext_3672_);
return v___x_3756_;
}
}
else
{
lean_object* v___x_3787_; 
lean_dec(v_a_3754_);
v___x_3787_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3680_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3789_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref_known(v___x_3787_, 1);
v___x_3789_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_3672_, v_stx_3671_, v_declName_3669_, v_attrKind_3670_, v_a_3788_, v_minIndexable_3674_, v_showInfo_3673_, v___x_3675_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3789_;
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_dec_ref(v_ext_3672_);
lean_dec(v_stx_3671_);
lean_dec(v_declName_3669_);
v_a_3790_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3787_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3787_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec_ref(v_ext_3672_);
lean_dec(v_stx_3671_);
lean_dec(v_declName_3669_);
v_a_3798_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3753_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3753_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
case 4:
{
lean_object* v___x_3806_; 
lean_dec(v_attrName_3676_);
lean_dec(v_stx_3671_);
v___x_3806_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_3672_, v_declName_3669_, v_attrKind_3670_, v___y_3679_, v___y_3680_);
return v___x_3806_;
}
case 5:
{
lean_object* v_prio_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
lean_dec_ref(v_ext_3672_);
lean_dec(v_stx_3671_);
v_prio_3807_ = lean_ctor_get(v_a_3705_, 0);
lean_inc(v_prio_3807_);
lean_dec_ref_known(v_a_3705_, 1);
v___x_3808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3809_ = lean_name_eq(v_attrName_3676_, v___x_3808_);
lean_dec(v_attrName_3676_);
if (v___x_3809_ == 0)
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
lean_dec(v_prio_3807_);
lean_dec(v_declName_3669_);
v___x_3810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10);
v___x_3811_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3810_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3811_;
}
else
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_3669_, v_attrKind_3670_, v_prio_3807_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3812_;
}
}
case 6:
{
lean_object* v___x_3813_; 
lean_dec(v_attrName_3676_);
lean_dec(v_stx_3671_);
v___x_3813_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_3672_, v_declName_3669_, v_attrKind_3670_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3813_;
}
case 7:
{
lean_object* v___x_3814_; 
lean_dec(v_attrName_3676_);
lean_dec(v_stx_3671_);
v___x_3814_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_3672_, v_declName_3669_, v_attrKind_3670_, v___y_3679_, v___y_3680_);
return v___x_3814_;
}
case 8:
{
uint8_t v_post_3815_; uint8_t v_inv_3816_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
lean_dec_ref(v_ext_3672_);
lean_dec(v_stx_3671_);
v_post_3815_ = lean_ctor_get_uint8(v_a_3705_, 0);
v_inv_3816_ = lean_ctor_get_uint8(v_a_3705_, 1);
lean_dec_ref_known(v_a_3705_, 0);
v___x_3824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3825_ = lean_name_eq(v_attrName_3676_, v___x_3824_);
lean_dec(v_attrName_3676_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
lean_dec(v_declName_3669_);
v___x_3826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12);
v___x_3827_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3826_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3827_;
}
else
{
v___y_3818_ = v___y_3677_;
v___y_3819_ = v___y_3678_;
v___y_3820_ = v___y_3679_;
v___y_3821_ = v___y_3680_;
goto v___jp_3817_;
}
v___jp_3817_:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3822_ = lean_unsigned_to_nat(1000u);
v___x_3823_ = l_Lean_Meta_Grind_addNormTheorem(v_declName_3669_, v_post_3815_, v_inv_3816_, v_attrKind_3670_, v___x_3822_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
return v___x_3823_;
}
}
case 9:
{
lean_object* v___x_3828_; uint8_t v___x_3829_; 
lean_dec_ref(v_ext_3672_);
lean_dec(v_stx_3671_);
v___x_3828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3829_ = lean_name_eq(v_attrName_3676_, v___x_3828_);
lean_dec(v_attrName_3676_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
lean_dec(v_declName_3669_);
v___x_3830_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14);
v___x_3831_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3830_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3831_;
}
else
{
goto v___jp_3682_;
}
}
case 10:
{
uint8_t v_fallback_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
lean_dec_ref(v_ext_3672_);
lean_dec(v_stx_3671_);
v_fallback_3832_ = lean_ctor_get_uint8(v_a_3705_, 0);
lean_dec_ref_known(v_a_3705_, 0);
v___x_3833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3834_ = lean_name_eq(v_attrName_3676_, v___x_3833_);
lean_dec(v_attrName_3676_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
lean_dec(v_declName_3669_);
v___x_3835_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16);
v___x_3836_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3835_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3836_;
}
else
{
lean_object* v___x_3837_; 
v___x_3837_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_3669_, v_attrKind_3670_, v_fallback_3832_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3837_;
}
}
default: 
{
lean_object* v___x_3838_; uint8_t v___x_3839_; 
lean_dec_ref(v_ext_3672_);
lean_dec(v_stx_3671_);
v___x_3838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3839_ = lean_name_eq(v_attrName_3676_, v___x_3838_);
lean_dec(v_attrName_3676_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_dec(v_declName_3669_);
v___x_3840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18);
v___x_3841_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3840_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3841_;
}
else
{
lean_object* v___x_3842_; 
v___x_3842_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_3669_, v_attrKind_3670_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3842_;
}
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec(v_attrName_3676_);
lean_dec_ref(v_ext_3672_);
lean_dec(v_stx_3671_);
lean_dec(v_declName_3669_);
v_a_3843_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3704_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3704_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
v___jp_3682_:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_Meta_Grind_addNormDeclToUnfold(v_declName_3669_, v_attrKind_3670_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3695_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3686_ = v___x_3683_;
v_isShared_3687_ = v_isSharedCheck_3695_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3683_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3695_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
uint8_t v___x_3688_; 
v___x_3688_ = lean_unbox(v_a_3684_);
lean_dec(v_a_3684_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_del_object(v___x_3686_);
v___x_3689_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_3690_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3689_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3690_;
}
else
{
lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3691_ = lean_box(0);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 0, v___x_3691_);
v___x_3693_ = v___x_3686_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
v_a_3696_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3683_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3683_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_declName_3851_, lean_object* v_attrKind_3852_, lean_object* v_stx_3853_, lean_object* v_ext_3854_, lean_object* v_showInfo_3855_, lean_object* v_minIndexable_3856_, lean_object* v___x_3857_, lean_object* v_attrName_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
uint8_t v_attrKind_boxed_3864_; uint8_t v_showInfo_boxed_3865_; uint8_t v_minIndexable_boxed_3866_; uint8_t v___x_11602__boxed_3867_; lean_object* v_res_3868_; 
v_attrKind_boxed_3864_ = lean_unbox(v_attrKind_3852_);
v_showInfo_boxed_3865_ = lean_unbox(v_showInfo_3855_);
v_minIndexable_boxed_3866_ = lean_unbox(v_minIndexable_3856_);
v___x_11602__boxed_3867_ = lean_unbox(v___x_3857_);
v_res_3868_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_declName_3851_, v_attrKind_boxed_3864_, v_stx_3853_, v_ext_3854_, v_showInfo_boxed_3865_, v_minIndexable_boxed_3866_, v___x_11602__boxed_3867_, v_attrName_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0(lean_object* v___x_3869_, lean_object* v_entry_3870_, lean_object* v_s_3871_){
_start:
{
lean_object* v_addEntryFn_3872_; lean_object* v_importedEntries_3873_; lean_object* v_state_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3882_; 
v_addEntryFn_3872_ = lean_ctor_get(v___x_3869_, 3);
lean_inc(v_addEntryFn_3872_);
lean_dec_ref(v___x_3869_);
v_importedEntries_3873_ = lean_ctor_get(v_s_3871_, 0);
v_state_3874_ = lean_ctor_get(v_s_3871_, 1);
v_isSharedCheck_3882_ = !lean_is_exclusive(v_s_3871_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3876_ = v_s_3871_;
v_isShared_3877_ = v_isSharedCheck_3882_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_state_3874_);
lean_inc(v_importedEntries_3873_);
lean_dec(v_s_3871_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3882_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v_state_3878_; lean_object* v___x_3880_; 
v_state_3878_ = lean_apply_2(v_addEntryFn_3872_, v_state_3874_, v_entry_3870_);
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 1, v_state_3878_);
v___x_3880_ = v___x_3876_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_importedEntries_3873_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v_state_3878_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_keys_3883_, lean_object* v_i_3884_, lean_object* v_k_3885_){
_start:
{
lean_object* v___x_3886_; uint8_t v___x_3887_; 
v___x_3886_ = lean_array_get_size(v_keys_3883_);
v___x_3887_ = lean_nat_dec_lt(v_i_3884_, v___x_3886_);
if (v___x_3887_ == 0)
{
lean_dec(v_i_3884_);
return v___x_3887_;
}
else
{
lean_object* v_k_x27_3888_; uint8_t v___x_3889_; 
v_k_x27_3888_ = lean_array_fget_borrowed(v_keys_3883_, v_i_3884_);
v___x_3889_ = l_Lean_instBEqExtraModUse_beq(v_k_3885_, v_k_x27_3888_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_unsigned_to_nat(1u);
v___x_3891_ = lean_nat_add(v_i_3884_, v___x_3890_);
lean_dec(v_i_3884_);
v_i_3884_ = v___x_3891_;
goto _start;
}
else
{
lean_dec(v_i_3884_);
return v___x_3887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_keys_3893_, lean_object* v_i_3894_, lean_object* v_k_3895_){
_start:
{
uint8_t v_res_3896_; lean_object* v_r_3897_; 
v_res_3896_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_keys_3893_, v_i_3894_, v_k_3895_);
lean_dec_ref(v_k_3895_);
lean_dec_ref(v_keys_3893_);
v_r_3897_ = lean_box(v_res_3896_);
return v_r_3897_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3898_, size_t v_x_3899_, lean_object* v_x_3900_){
_start:
{
if (lean_obj_tag(v_x_3898_) == 0)
{
lean_object* v_es_3901_; lean_object* v___x_3902_; size_t v___x_3903_; size_t v___x_3904_; lean_object* v_j_3905_; lean_object* v___x_3906_; 
v_es_3901_ = lean_ctor_get(v_x_3898_, 0);
v___x_3902_ = lean_box(2);
v___x_3903_ = ((size_t)31ULL);
v___x_3904_ = lean_usize_land(v_x_3899_, v___x_3903_);
v_j_3905_ = lean_usize_to_nat(v___x_3904_);
v___x_3906_ = lean_array_get_borrowed(v___x_3902_, v_es_3901_, v_j_3905_);
lean_dec(v_j_3905_);
switch(lean_obj_tag(v___x_3906_))
{
case 0:
{
lean_object* v_key_3907_; uint8_t v___x_3908_; 
v_key_3907_ = lean_ctor_get(v___x_3906_, 0);
v___x_3908_ = l_Lean_instBEqExtraModUse_beq(v_x_3900_, v_key_3907_);
return v___x_3908_;
}
case 1:
{
lean_object* v_node_3909_; size_t v___x_3910_; size_t v___x_3911_; 
v_node_3909_ = lean_ctor_get(v___x_3906_, 0);
v___x_3910_ = ((size_t)5ULL);
v___x_3911_ = lean_usize_shift_right(v_x_3899_, v___x_3910_);
v_x_3898_ = v_node_3909_;
v_x_3899_ = v___x_3911_;
goto _start;
}
default: 
{
uint8_t v___x_3913_; 
v___x_3913_ = 0;
return v___x_3913_;
}
}
}
else
{
lean_object* v_ks_3914_; lean_object* v___x_3915_; uint8_t v___x_3916_; 
v_ks_3914_ = lean_ctor_get(v_x_3898_, 0);
v___x_3915_ = lean_unsigned_to_nat(0u);
v___x_3916_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_ks_3914_, v___x_3915_, v_x_3900_);
return v___x_3916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_x_3917_, lean_object* v_x_3918_, lean_object* v_x_3919_){
_start:
{
size_t v_x_12028__boxed_3920_; uint8_t v_res_3921_; lean_object* v_r_3922_; 
v_x_12028__boxed_3920_ = lean_unbox_usize(v_x_3918_);
lean_dec(v_x_3918_);
v_res_3921_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_3917_, v_x_12028__boxed_3920_, v_x_3919_);
lean_dec_ref(v_x_3919_);
lean_dec_ref(v_x_3917_);
v_r_3922_ = lean_box(v_res_3921_);
return v_r_3922_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3923_, lean_object* v_x_3924_){
_start:
{
uint64_t v___x_3925_; size_t v___x_3926_; uint8_t v___x_3927_; 
v___x_3925_ = l_Lean_instHashableExtraModUse_hash(v_x_3924_);
v___x_3926_ = lean_uint64_to_usize(v___x_3925_);
v___x_3927_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_3923_, v___x_3926_, v_x_3924_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3928_, lean_object* v_x_3929_){
_start:
{
uint8_t v_res_3930_; lean_object* v_r_3931_; 
v_res_3930_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v_x_3928_, v_x_3929_);
lean_dec_ref(v_x_3929_);
lean_dec_ref(v_x_3928_);
v_r_3931_ = lean_box(v_res_3930_);
return v_r_3931_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_3932_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3));
v___x_3938_ = l_Lean_stringToMessageData(v___x_3937_);
return v___x_3938_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6(void){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3940_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5));
v___x_3941_ = l_Lean_stringToMessageData(v___x_3940_);
return v___x_3941_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7(void){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_3943_ = l_Lean_stringToMessageData(v___x_3942_);
return v___x_3943_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v_cls_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v_cls_3944_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_3945_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1));
v___x_3946_ = l_Lean_Name_append(v___x_3945_, v_cls_3944_);
return v___x_3946_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3948_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9));
v___x_3949_ = l_Lean_stringToMessageData(v___x_3948_);
return v___x_3949_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12(void){
_start:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11));
v___x_3952_ = l_Lean_stringToMessageData(v___x_3951_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(lean_object* v_mod_3957_, uint8_t v_isMeta_3958_, lean_object* v_hint_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v_env_3999_; uint8_t v_isExporting_4000_; lean_object* v_entry_4001_; lean_object* v___x_4002_; lean_object* v_env_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v___x_3997_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0);
v___x_3998_ = lean_st_ref_get(v___y_3963_);
v_env_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc_ref(v_env_3999_);
lean_dec(v___x_3998_);
v_isExporting_4000_ = lean_ctor_get_uint8(v_env_3999_, sizeof(void*)*13);
lean_dec_ref(v_env_3999_);
lean_inc(v_mod_3957_);
v_entry_4001_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_4001_, 0, v_mod_3957_);
lean_ctor_set_uint8(v_entry_4001_, sizeof(void*)*1, v_isExporting_4000_);
lean_ctor_set_uint8(v_entry_4001_, sizeof(void*)*1 + 1, v_isMeta_3958_);
v___x_4002_ = lean_st_ref_get(v___y_3963_);
v_env_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc_ref(v_env_4003_);
lean_dec(v___x_4002_);
v___x_4004_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_4005_ = lean_box(1);
v___x_4006_ = lean_box(0);
v___x_4007_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3997_, v___x_4004_, v_env_4003_, v___x_4005_, v___x_4006_);
v___x_4008_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v___x_4007_, v_entry_4001_);
lean_dec(v___x_4007_);
if (v___x_4008_ == 0)
{
lean_object* v_toCold_4009_; lean_object* v_options_4010_; lean_object* v_inheritedTraceOptions_4011_; uint8_t v_hasTrace_4012_; lean_object* v___f_4013_; uint8_t v___x_4014_; lean_object* v___y_4016_; lean_object* v___y_4017_; 
v_toCold_4009_ = lean_ctor_get(v___y_3962_, 0);
v_options_4010_ = lean_ctor_get(v_toCold_4009_, 2);
v_inheritedTraceOptions_4011_ = lean_ctor_get(v_toCold_4009_, 11);
v_hasTrace_4012_ = lean_ctor_get_uint8(v_options_4010_, sizeof(void*)*1);
v___f_4013_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_4013_, 0, v___x_4004_);
lean_closure_set(v___f_4013_, 1, v_entry_4001_);
v___x_4014_ = 1;
if (v_hasTrace_4012_ == 0)
{
lean_dec(v_hint_3959_);
lean_dec(v_mod_3957_);
v___y_4016_ = v___y_3961_;
v___y_4017_ = v___y_3963_;
goto v___jp_4015_;
}
else
{
lean_object* v_cls_4044_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___x_4064_; uint8_t v___x_4065_; 
v_cls_4044_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_4064_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8);
v___x_4065_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4011_, v_options_4010_, v___x_4064_);
if (v___x_4065_ == 0)
{
lean_dec(v_hint_3959_);
lean_dec(v_mod_3957_);
v___y_4016_ = v___y_3961_;
v___y_4017_ = v___y_3963_;
goto v___jp_4015_;
}
else
{
lean_object* v___x_4066_; lean_object* v___y_4068_; 
v___x_4066_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10);
if (v_isExporting_4000_ == 0)
{
lean_object* v___x_4075_; 
v___x_4075_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15));
v___y_4068_ = v___x_4075_;
goto v___jp_4067_;
}
else
{
lean_object* v___x_4076_; 
v___x_4076_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16));
v___y_4068_ = v___x_4076_;
goto v___jp_4067_;
}
v___jp_4067_:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
lean_inc_ref(v___y_4068_);
v___x_4069_ = l_Lean_stringToMessageData(v___y_4068_);
v___x_4070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4066_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12);
v___x_4072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4070_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
if (v_isMeta_3958_ == 0)
{
lean_object* v___x_4073_; 
v___x_4073_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13));
v___y_4051_ = v___x_4072_;
v___y_4052_ = v___x_4073_;
goto v___jp_4050_;
}
else
{
lean_object* v___x_4074_; 
v___x_4074_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14));
v___y_4051_ = v___x_4072_;
v___y_4052_ = v___x_4074_;
goto v___jp_4050_;
}
}
}
v___jp_4045_:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___y_4046_);
lean_ctor_set(v___x_4048_, 1, v___y_4047_);
v___x_4049_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_4044_, v___x_4048_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_dec_ref_known(v___x_4049_, 1);
v___y_4016_ = v___y_3961_;
v___y_4017_ = v___y_3963_;
goto v___jp_4015_;
}
else
{
lean_dec_ref(v___f_4013_);
return v___x_4049_;
}
}
v___jp_4050_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; 
lean_inc_ref(v___y_4052_);
v___x_4053_ = l_Lean_stringToMessageData(v___y_4052_);
v___x_4054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___y_4051_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4);
v___x_4056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4054_);
lean_ctor_set(v___x_4056_, 1, v___x_4055_);
v___x_4057_ = l_Lean_MessageData_ofName(v_mod_3957_);
v___x_4058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4056_);
lean_ctor_set(v___x_4058_, 1, v___x_4057_);
v___x_4059_ = l_Lean_Name_isAnonymous(v_hint_3959_);
if (v___x_4059_ == 0)
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4060_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6);
v___x_4061_ = l_Lean_MessageData_ofName(v_hint_3959_);
v___x_4062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4060_);
lean_ctor_set(v___x_4062_, 1, v___x_4061_);
v___y_4046_ = v___x_4058_;
v___y_4047_ = v___x_4062_;
goto v___jp_4045_;
}
else
{
lean_object* v___x_4063_; 
lean_dec(v_hint_3959_);
v___x_4063_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7);
v___y_4046_ = v___x_4058_;
v___y_4047_ = v___x_4063_;
goto v___jp_4045_;
}
}
}
v___jp_4015_:
{
lean_object* v___x_4018_; lean_object* v_toEnvExtension_4019_; uint8_t v_logWrites_4020_; 
v___x_4018_ = lean_st_ref_take(v___y_4017_);
v_toEnvExtension_4019_ = lean_ctor_get(v___x_4004_, 0);
v_logWrites_4020_ = lean_ctor_get_uint8(v_toEnvExtension_4019_, sizeof(void*)*6);
if (v_logWrites_4020_ == 0)
{
lean_object* v_env_4021_; lean_object* v_nextMacroScope_4022_; lean_object* v_ngen_4023_; lean_object* v_auxDeclNGen_4024_; lean_object* v_traceState_4025_; lean_object* v_recordedDeps_4026_; lean_object* v_messages_4027_; lean_object* v_infoState_4028_; lean_object* v_snapshotTasks_4029_; lean_object* v_asyncMode_4030_; lean_object* v___x_4031_; 
v_env_4021_ = lean_ctor_get(v___x_4018_, 0);
lean_inc_ref(v_env_4021_);
v_nextMacroScope_4022_ = lean_ctor_get(v___x_4018_, 1);
lean_inc(v_nextMacroScope_4022_);
v_ngen_4023_ = lean_ctor_get(v___x_4018_, 2);
lean_inc_ref(v_ngen_4023_);
v_auxDeclNGen_4024_ = lean_ctor_get(v___x_4018_, 3);
lean_inc_ref(v_auxDeclNGen_4024_);
v_traceState_4025_ = lean_ctor_get(v___x_4018_, 4);
lean_inc_ref(v_traceState_4025_);
v_recordedDeps_4026_ = lean_ctor_get(v___x_4018_, 6);
lean_inc_ref(v_recordedDeps_4026_);
v_messages_4027_ = lean_ctor_get(v___x_4018_, 7);
lean_inc_ref(v_messages_4027_);
v_infoState_4028_ = lean_ctor_get(v___x_4018_, 8);
lean_inc_ref(v_infoState_4028_);
v_snapshotTasks_4029_ = lean_ctor_get(v___x_4018_, 9);
lean_inc_ref(v_snapshotTasks_4029_);
lean_dec(v___x_4018_);
v_asyncMode_4030_ = lean_ctor_get(v_toEnvExtension_4019_, 2);
lean_inc_ref(v_toEnvExtension_4019_);
v___x_4031_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4019_, v_env_4021_, v___f_4013_, v_asyncMode_4030_, v___x_4006_, v___x_4014_);
v___y_3966_ = v_recordedDeps_4026_;
v___y_3967_ = v_ngen_4023_;
v___y_3968_ = v___y_4017_;
v___y_3969_ = v_snapshotTasks_4029_;
v___y_3970_ = v_messages_4027_;
v___y_3971_ = v_auxDeclNGen_4024_;
v___y_3972_ = v_infoState_4028_;
v___y_3973_ = v___y_4016_;
v___y_3974_ = v_nextMacroScope_4022_;
v___y_3975_ = v_traceState_4025_;
v___y_3976_ = v___x_4031_;
goto v___jp_3965_;
}
else
{
lean_object* v_env_4032_; lean_object* v_nextMacroScope_4033_; lean_object* v_ngen_4034_; lean_object* v_auxDeclNGen_4035_; lean_object* v_traceState_4036_; lean_object* v_recordedDeps_4037_; lean_object* v_messages_4038_; lean_object* v_infoState_4039_; lean_object* v_snapshotTasks_4040_; lean_object* v_asyncMode_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v_env_4032_ = lean_ctor_get(v___x_4018_, 0);
lean_inc_ref(v_env_4032_);
v_nextMacroScope_4033_ = lean_ctor_get(v___x_4018_, 1);
lean_inc(v_nextMacroScope_4033_);
v_ngen_4034_ = lean_ctor_get(v___x_4018_, 2);
lean_inc_ref(v_ngen_4034_);
v_auxDeclNGen_4035_ = lean_ctor_get(v___x_4018_, 3);
lean_inc_ref(v_auxDeclNGen_4035_);
v_traceState_4036_ = lean_ctor_get(v___x_4018_, 4);
lean_inc_ref(v_traceState_4036_);
v_recordedDeps_4037_ = lean_ctor_get(v___x_4018_, 6);
lean_inc_ref(v_recordedDeps_4037_);
v_messages_4038_ = lean_ctor_get(v___x_4018_, 7);
lean_inc_ref(v_messages_4038_);
v_infoState_4039_ = lean_ctor_get(v___x_4018_, 8);
lean_inc_ref(v_infoState_4039_);
v_snapshotTasks_4040_ = lean_ctor_get(v___x_4018_, 9);
lean_inc_ref(v_snapshotTasks_4040_);
lean_dec(v___x_4018_);
v_asyncMode_4041_ = lean_ctor_get(v_toEnvExtension_4019_, 2);
lean_inc_ref_n(v_toEnvExtension_4019_, 2);
v___x_4042_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4019_, v_env_4032_);
lean_dec_ref(v_env_4032_);
v___x_4043_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4019_, v___x_4042_, v___f_4013_, v_asyncMode_4041_, v___x_4006_, v___x_4014_);
v___y_3966_ = v_recordedDeps_4037_;
v___y_3967_ = v_ngen_4034_;
v___y_3968_ = v___y_4017_;
v___y_3969_ = v_snapshotTasks_4040_;
v___y_3970_ = v_messages_4038_;
v___y_3971_ = v_auxDeclNGen_4035_;
v___y_3972_ = v_infoState_4039_;
v___y_3973_ = v___y_4016_;
v___y_3974_ = v_nextMacroScope_4033_;
v___y_3975_ = v_traceState_4036_;
v___y_3976_ = v___x_4043_;
goto v___jp_3965_;
}
}
}
else
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
lean_dec_ref_known(v_entry_4001_, 1);
lean_dec(v_hint_3959_);
lean_dec(v_mod_3957_);
v___x_4077_ = lean_box(0);
v___x_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
return v___x_4078_;
}
v___jp_3965_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v_mctx_3981_; lean_object* v_zetaDeltaFVarIds_3982_; lean_object* v_postponed_3983_; lean_object* v_diag_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3995_; 
v___x_3977_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
v___x_3978_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3978_, 0, v___y_3976_);
lean_ctor_set(v___x_3978_, 1, v___y_3974_);
lean_ctor_set(v___x_3978_, 2, v___y_3967_);
lean_ctor_set(v___x_3978_, 3, v___y_3971_);
lean_ctor_set(v___x_3978_, 4, v___y_3975_);
lean_ctor_set(v___x_3978_, 5, v___x_3977_);
lean_ctor_set(v___x_3978_, 6, v___y_3966_);
lean_ctor_set(v___x_3978_, 7, v___y_3970_);
lean_ctor_set(v___x_3978_, 8, v___y_3972_);
lean_ctor_set(v___x_3978_, 9, v___y_3969_);
v___x_3979_ = lean_st_ref_put(v___y_3968_, v___x_3978_);
v___x_3980_ = lean_st_ref_take(v___y_3973_);
v_mctx_3981_ = lean_ctor_get(v___x_3980_, 0);
v_zetaDeltaFVarIds_3982_ = lean_ctor_get(v___x_3980_, 2);
v_postponed_3983_ = lean_ctor_get(v___x_3980_, 3);
v_diag_3984_ = lean_ctor_get(v___x_3980_, 4);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3995_ == 0)
{
lean_object* v_unused_3996_; 
v_unused_3996_ = lean_ctor_get(v___x_3980_, 1);
lean_dec(v_unused_3996_);
v___x_3986_ = v___x_3980_;
v_isShared_3987_ = v_isSharedCheck_3995_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_diag_3984_);
lean_inc(v_postponed_3983_);
lean_inc(v_zetaDeltaFVarIds_3982_);
lean_inc(v_mctx_3981_);
lean_dec(v___x_3980_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3995_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3988_ = lean_box(0);
v___x_3989_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 1, v___x_3989_);
v___x_3991_ = v___x_3986_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_mctx_3981_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v___x_3989_);
lean_ctor_set(v_reuseFailAlloc_3994_, 2, v_zetaDeltaFVarIds_3982_);
lean_ctor_set(v_reuseFailAlloc_3994_, 3, v_postponed_3983_);
lean_ctor_set(v_reuseFailAlloc_3994_, 4, v_diag_3984_);
v___x_3991_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3992_ = lean_st_ref_put(v___y_3973_, v___x_3991_);
v___x_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3988_);
return v___x_3993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___boxed(lean_object* v_mod_4079_, lean_object* v_isMeta_4080_, lean_object* v_hint_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
uint8_t v_isMeta_boxed_4087_; lean_object* v_res_4088_; 
v_isMeta_boxed_4087_ = lean_unbox(v_isMeta_4080_);
v_res_4088_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_mod_4079_, v_isMeta_boxed_4087_, v_hint_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(lean_object* v_a_4089_, lean_object* v_x_4090_){
_start:
{
if (lean_obj_tag(v_x_4090_) == 0)
{
lean_object* v___x_4091_; 
v___x_4091_ = lean_box(0);
return v___x_4091_;
}
else
{
lean_object* v_key_4092_; lean_object* v_value_4093_; lean_object* v_tail_4094_; uint8_t v___x_4095_; 
v_key_4092_ = lean_ctor_get(v_x_4090_, 0);
v_value_4093_ = lean_ctor_get(v_x_4090_, 1);
v_tail_4094_ = lean_ctor_get(v_x_4090_, 2);
v___x_4095_ = lean_name_eq(v_key_4092_, v_a_4089_);
if (v___x_4095_ == 0)
{
v_x_4090_ = v_tail_4094_;
goto _start;
}
else
{
lean_object* v___x_4097_; 
lean_inc(v_value_4093_);
v___x_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4097_, 0, v_value_4093_);
return v___x_4097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_4098_, lean_object* v_x_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4098_, v_x_4099_);
lean_dec(v_x_4099_);
lean_dec(v_a_4098_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(lean_object* v_m_4101_, lean_object* v_a_4102_){
_start:
{
lean_object* v_buckets_4103_; lean_object* v___x_4104_; uint64_t v___y_4106_; 
v_buckets_4103_ = lean_ctor_get(v_m_4101_, 1);
v___x_4104_ = lean_array_get_size(v_buckets_4103_);
if (lean_obj_tag(v_a_4102_) == 0)
{
uint64_t v___x_4120_; 
v___x_4120_ = 1723ULL;
v___y_4106_ = v___x_4120_;
goto v___jp_4105_;
}
else
{
uint64_t v_hash_4121_; 
v_hash_4121_ = lean_ctor_get_uint64(v_a_4102_, sizeof(void*)*2);
v___y_4106_ = v_hash_4121_;
goto v___jp_4105_;
}
v___jp_4105_:
{
uint64_t v___x_4107_; uint64_t v___x_4108_; uint64_t v_fold_4109_; uint64_t v___x_4110_; uint64_t v___x_4111_; uint64_t v___x_4112_; size_t v___x_4113_; size_t v___x_4114_; size_t v___x_4115_; size_t v___x_4116_; size_t v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4107_ = 32ULL;
v___x_4108_ = lean_uint64_shift_right(v___y_4106_, v___x_4107_);
v_fold_4109_ = lean_uint64_xor(v___y_4106_, v___x_4108_);
v___x_4110_ = 16ULL;
v___x_4111_ = lean_uint64_shift_right(v_fold_4109_, v___x_4110_);
v___x_4112_ = lean_uint64_xor(v_fold_4109_, v___x_4111_);
v___x_4113_ = lean_uint64_to_usize(v___x_4112_);
v___x_4114_ = lean_usize_of_nat(v___x_4104_);
v___x_4115_ = ((size_t)1ULL);
v___x_4116_ = lean_usize_sub(v___x_4114_, v___x_4115_);
v___x_4117_ = lean_usize_land(v___x_4113_, v___x_4116_);
v___x_4118_ = lean_array_uget_borrowed(v_buckets_4103_, v___x_4117_);
v___x_4119_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4102_, v___x_4118_);
return v___x_4119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg___boxed(lean_object* v_m_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v_m_4122_, v_a_4123_);
lean_dec(v_a_4123_);
lean_dec_ref(v_m_4122_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v___x_4125_, lean_object* v_declName_4126_, lean_object* v_as_4127_, size_t v_sz_4128_, size_t v_i_4129_, lean_object* v_b_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
uint8_t v___x_4136_; 
v___x_4136_ = lean_usize_dec_lt(v_i_4129_, v_sz_4128_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; 
lean_dec(v_declName_4126_);
v___x_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4137_, 0, v_b_4130_);
return v___x_4137_;
}
else
{
lean_object* v___x_4138_; lean_object* v_modules_4139_; lean_object* v___x_4140_; lean_object* v_a_4141_; lean_object* v___x_4142_; lean_object* v_toImport_4143_; lean_object* v_module_4144_; lean_object* v___x_4145_; uint8_t v___x_4146_; lean_object* v___x_4147_; 
v___x_4138_ = l_Lean_Environment_header(v___x_4125_);
v_modules_4139_ = lean_ctor_get(v___x_4138_, 3);
lean_inc_ref(v_modules_4139_);
lean_dec_ref(v___x_4138_);
v___x_4140_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_4141_ = lean_array_uget_borrowed(v_as_4127_, v_i_4129_);
v___x_4142_ = lean_array_get(v___x_4140_, v_modules_4139_, v_a_4141_);
lean_dec_ref(v_modules_4139_);
v_toImport_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc_ref(v_toImport_4143_);
lean_dec(v___x_4142_);
v_module_4144_ = lean_ctor_get(v_toImport_4143_, 0);
lean_inc(v_module_4144_);
lean_dec_ref(v_toImport_4143_);
v___x_4145_ = lean_box(0);
v___x_4146_ = 0;
lean_inc(v_declName_4126_);
v___x_4147_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_module_4144_, v___x_4146_, v_declName_4126_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
if (lean_obj_tag(v___x_4147_) == 0)
{
size_t v___x_4148_; size_t v___x_4149_; 
lean_dec_ref_known(v___x_4147_, 1);
v___x_4148_ = ((size_t)1ULL);
v___x_4149_ = lean_usize_add(v_i_4129_, v___x_4148_);
v_i_4129_ = v___x_4149_;
v_b_4130_ = v___x_4145_;
goto _start;
}
else
{
lean_dec(v_declName_4126_);
return v___x_4147_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v___x_4151_, lean_object* v_declName_4152_, lean_object* v_as_4153_, lean_object* v_sz_4154_, lean_object* v_i_4155_, lean_object* v_b_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
size_t v_sz_boxed_4162_; size_t v_i_boxed_4163_; lean_object* v_res_4164_; 
v_sz_boxed_4162_ = lean_unbox_usize(v_sz_4154_);
lean_dec(v_sz_4154_);
v_i_boxed_4163_ = lean_unbox_usize(v_i_4155_);
lean_dec(v_i_4155_);
v_res_4164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v___x_4151_, v_declName_4152_, v_as_4153_, v_sz_boxed_4162_, v_i_boxed_4163_, v_b_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec_ref(v_as_4153_);
lean_dec_ref(v___x_4151_);
return v_res_4164_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4165_; 
v___x_4165_ = l_Std_HashMap_instInhabited___redArg();
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_4168_, uint8_t v_isMeta_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v_env_4180_; lean_object* v___y_4182_; lean_object* v___x_4195_; 
v___x_4175_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_4176_ = lean_st_ref_get(v___y_4173_);
v_env_4180_ = lean_ctor_get(v___x_4176_, 0);
lean_inc_ref(v_env_4180_);
lean_dec(v___x_4176_);
v___x_4195_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4180_, v_declName_4168_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_dec_ref(v_env_4180_);
lean_dec(v_declName_4168_);
goto v___jp_4177_;
}
else
{
lean_object* v_val_4196_; lean_object* v___x_4197_; lean_object* v_modules_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; 
v_val_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_val_4196_);
lean_dec_ref_known(v___x_4195_, 1);
v___x_4197_ = l_Lean_Environment_header(v_env_4180_);
v_modules_4198_ = lean_ctor_get(v___x_4197_, 3);
lean_inc_ref(v_modules_4198_);
lean_dec_ref(v___x_4197_);
v___x_4199_ = lean_array_get_size(v_modules_4198_);
v___x_4200_ = lean_nat_dec_lt(v_val_4196_, v___x_4199_);
if (v___x_4200_ == 0)
{
lean_dec_ref(v_modules_4198_);
lean_dec(v_val_4196_);
lean_dec_ref(v_env_4180_);
lean_dec(v_declName_4168_);
goto v___jp_4177_;
}
else
{
lean_object* v___x_4201_; lean_object* v___x_4202_; uint8_t v___y_4204_; 
v___x_4201_ = lean_array_fget(v_modules_4198_, v_val_4196_);
lean_dec(v_val_4196_);
lean_dec_ref(v_modules_4198_);
v___x_4202_ = lean_st_ref_get(v___y_4173_);
if (v_isMeta_4169_ == 0)
{
lean_dec(v___x_4202_);
v___y_4204_ = v_isMeta_4169_;
goto v___jp_4203_;
}
else
{
lean_object* v_env_4215_; uint8_t v___x_4216_; 
v_env_4215_ = lean_ctor_get(v___x_4202_, 0);
lean_inc_ref(v_env_4215_);
lean_dec(v___x_4202_);
lean_inc(v_declName_4168_);
v___x_4216_ = l_Lean_isMarkedMeta(v_env_4215_, v_declName_4168_);
if (v___x_4216_ == 0)
{
v___y_4204_ = v_isMeta_4169_;
goto v___jp_4203_;
}
else
{
uint8_t v___x_4217_; 
v___x_4217_ = 0;
v___y_4204_ = v___x_4217_;
goto v___jp_4203_;
}
}
v___jp_4203_:
{
lean_object* v_toImport_4205_; lean_object* v_module_4206_; lean_object* v___x_4207_; 
v_toImport_4205_ = lean_ctor_get(v___x_4201_, 0);
lean_inc_ref(v_toImport_4205_);
lean_dec(v___x_4201_);
v_module_4206_ = lean_ctor_get(v_toImport_4205_, 0);
lean_inc(v_module_4206_);
lean_dec_ref(v_toImport_4205_);
lean_inc(v_declName_4168_);
v___x_4207_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_module_4206_, v___y_4204_, v_declName_4168_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_dec_ref_known(v___x_4207_, 1);
v___x_4208_ = l_Lean_indirectModUseExt;
v___x_4209_ = lean_box(1);
v___x_4210_ = lean_box(0);
lean_inc_ref(v_env_4180_);
v___x_4211_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4175_, v___x_4208_, v_env_4180_, v___x_4209_, v___x_4210_);
v___x_4212_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4211_, v_declName_4168_);
lean_dec(v___x_4211_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v___x_4213_; 
v___x_4213_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_4182_ = v___x_4213_;
goto v___jp_4181_;
}
else
{
lean_object* v_val_4214_; 
v_val_4214_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_val_4214_);
lean_dec_ref_known(v___x_4212_, 1);
v___y_4182_ = v_val_4214_;
goto v___jp_4181_;
}
}
else
{
lean_dec_ref(v_env_4180_);
lean_dec(v_declName_4168_);
return v___x_4207_;
}
}
}
}
v___jp_4177_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = lean_box(0);
v___x_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
return v___x_4179_;
}
v___jp_4181_:
{
lean_object* v___x_4183_; size_t v_sz_4184_; size_t v___x_4185_; lean_object* v___x_4186_; 
v___x_4183_ = lean_box(0);
v_sz_4184_ = lean_array_size(v___y_4182_);
v___x_4185_ = ((size_t)0ULL);
v___x_4186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_env_4180_, v_declName_4168_, v___y_4182_, v_sz_4184_, v___x_4185_, v___x_4183_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
lean_dec_ref(v___y_4182_);
lean_dec_ref(v_env_4180_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4193_ == 0)
{
lean_object* v_unused_4194_; 
v_unused_4194_ = lean_ctor_get(v___x_4186_, 0);
lean_dec(v_unused_4194_);
v___x_4188_ = v___x_4186_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_dec(v___x_4186_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 0, v___x_4183_);
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4183_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
else
{
return v___x_4186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_4218_, lean_object* v_isMeta_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
uint8_t v_isMeta_boxed_4225_; lean_object* v_res_4226_; 
v_isMeta_boxed_4225_ = lean_unbox(v_isMeta_4219_);
v_res_4226_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_4218_, v_isMeta_boxed_4225_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_4227_, uint8_t v_when_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
if (v_when_4228_ == 0)
{
lean_object* v___x_4234_; 
lean_inc(v___y_4232_);
lean_inc_ref(v___y_4231_);
lean_inc(v___y_4230_);
lean_inc_ref(v___y_4229_);
v___x_4234_ = lean_apply_5(v_x_4227_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, lean_box(0));
return v___x_4234_;
}
else
{
uint8_t v___x_4235_; lean_object* v___x_4236_; 
v___x_4235_ = 0;
v___x_4236_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_4227_, v___x_4235_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
return v___x_4236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_4237_, lean_object* v_when_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
uint8_t v_when_boxed_4244_; lean_object* v_res_4245_; 
v_when_boxed_4244_ = lean_unbox(v_when_4238_);
v_res_4245_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_4237_, v_when_boxed_4244_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v_ext_4246_, uint8_t v_showInfo_4247_, uint8_t v_minIndexable_4248_, lean_object* v_attrName_4249_, lean_object* v___x_4250_, lean_object* v_declName_4251_, lean_object* v_stx_4252_, uint8_t v_attrKind_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
uint8_t v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___f_4262_; uint8_t v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4257_ = 0;
v___x_4258_ = lean_box(v_attrKind_4253_);
v___x_4259_ = lean_box(v_showInfo_4247_);
v___x_4260_ = lean_box(v_minIndexable_4248_);
v___x_4261_ = lean_box(v___x_4257_);
lean_inc(v_declName_4251_);
v___f_4262_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_4262_, 0, v_declName_4251_);
lean_closure_set(v___f_4262_, 1, v___x_4258_);
lean_closure_set(v___f_4262_, 2, v_stx_4252_);
lean_closure_set(v___f_4262_, 3, v_ext_4246_);
lean_closure_set(v___f_4262_, 4, v___x_4259_);
lean_closure_set(v___f_4262_, 5, v___x_4260_);
lean_closure_set(v___f_4262_, 6, v___x_4261_);
lean_closure_set(v___f_4262_, 7, v_attrName_4249_);
v___x_4263_ = 1;
v___x_4264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_4265_ = lean_unsigned_to_nat(32u);
v___x_4266_ = lean_mk_empty_array_with_capacity(v___x_4265_);
lean_dec_ref(v___x_4266_);
v___x_4267_ = lean_unsigned_to_nat(0u);
v___x_4268_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_4269_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_4270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_4271_ = lean_box(0);
lean_inc(v___x_4250_);
v___x_4272_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4272_, 0, v___x_4264_);
lean_ctor_set(v___x_4272_, 1, v___x_4250_);
lean_ctor_set(v___x_4272_, 2, v___x_4269_);
lean_ctor_set(v___x_4272_, 3, v___x_4270_);
lean_ctor_set(v___x_4272_, 4, v___x_4271_);
lean_ctor_set(v___x_4272_, 5, v___x_4267_);
lean_ctor_set(v___x_4272_, 6, v___x_4271_);
lean_ctor_set_uint8(v___x_4272_, sizeof(void*)*7, v___x_4257_);
lean_ctor_set_uint8(v___x_4272_, sizeof(void*)*7 + 1, v___x_4257_);
lean_ctor_set_uint8(v___x_4272_, sizeof(void*)*7 + 2, v___x_4257_);
lean_ctor_set_uint8(v___x_4272_, sizeof(void*)*7 + 3, v___x_4263_);
v___x_4273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_4274_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_4275_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_4276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4273_);
lean_ctor_set(v___x_4276_, 1, v___x_4274_);
lean_ctor_set(v___x_4276_, 2, v___x_4250_);
lean_ctor_set(v___x_4276_, 3, v___x_4268_);
lean_ctor_set(v___x_4276_, 4, v___x_4275_);
v___x_4277_ = lean_st_mk_ref(v___x_4276_);
v___x_4278_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_4251_, v___x_4257_, v___x_4272_, v___x_4277_, v___y_4254_, v___y_4255_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v___x_4279_; 
lean_dec_ref_known(v___x_4278_, 1);
v___x_4279_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_4262_, v___x_4263_, v___x_4272_, v___x_4277_, v___y_4254_, v___y_4255_);
lean_dec_ref_known(v___x_4272_, 7);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4288_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4282_ = v___x_4279_;
v_isShared_4283_ = v_isSharedCheck_4288_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4279_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4288_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4284_; lean_object* v___x_4286_; 
v___x_4284_ = lean_st_ref_get(v___x_4277_);
lean_dec(v___x_4277_);
lean_dec(v___x_4284_);
if (v_isShared_4283_ == 0)
{
v___x_4286_ = v___x_4282_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4280_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
else
{
lean_dec(v___x_4277_);
return v___x_4279_;
}
}
else
{
lean_dec(v___x_4277_);
lean_dec_ref_known(v___x_4272_, 7);
lean_dec_ref(v___f_4262_);
return v___x_4278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v_ext_4289_, lean_object* v_showInfo_4290_, lean_object* v_minIndexable_4291_, lean_object* v_attrName_4292_, lean_object* v___x_4293_, lean_object* v_declName_4294_, lean_object* v_stx_4295_, lean_object* v_attrKind_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
uint8_t v_showInfo_boxed_4300_; uint8_t v_minIndexable_boxed_4301_; uint8_t v_attrKind_boxed_4302_; lean_object* v_res_4303_; 
v_showInfo_boxed_4300_ = lean_unbox(v_showInfo_4290_);
v_minIndexable_boxed_4301_ = lean_unbox(v_minIndexable_4291_);
v_attrKind_boxed_4302_ = lean_unbox(v_attrKind_4296_);
v_res_4303_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v_ext_4289_, v_showInfo_boxed_4300_, v_minIndexable_boxed_4301_, v_attrName_4292_, v___x_4293_, v_declName_4294_, v_stx_4295_, v_attrKind_boxed_4302_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_4326_, uint8_t v_minIndexable_4327_, uint8_t v_showInfo_4328_, lean_object* v_ext_4329_, lean_object* v_ref_4330_){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___f_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___f_4337_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4383_; 
v___x_4332_ = lean_box(1);
v___x_4333_ = lean_box(v_showInfo_4328_);
lean_inc_n(v_attrName_4326_, 2);
lean_inc_ref(v_ext_4329_);
v___f_4334_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_4334_, 0, v_ext_4329_);
lean_closure_set(v___f_4334_, 1, v___x_4332_);
lean_closure_set(v___f_4334_, 2, v___x_4333_);
lean_closure_set(v___f_4334_, 3, v_attrName_4326_);
v___x_4335_ = lean_box(v_showInfo_4328_);
v___x_4336_ = lean_box(v_minIndexable_4327_);
v___f_4337_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_4337_, 0, v_ext_4329_);
lean_closure_set(v___f_4337_, 1, v___x_4335_);
lean_closure_set(v___f_4337_, 2, v___x_4336_);
lean_closure_set(v___f_4337_, 3, v_attrName_4326_);
lean_closure_set(v___f_4337_, 4, v___x_4332_);
if (v_minIndexable_4327_ == 0)
{
if (v_showInfo_4328_ == 0)
{
lean_inc(v_attrName_4326_);
v___y_4383_ = v_attrName_4326_;
goto v___jp_4382_;
}
else
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_4326_);
v___x_4412_ = lean_name_append_after(v_attrName_4326_, v___x_4411_);
v___y_4383_ = v___x_4412_;
goto v___jp_4382_;
}
}
else
{
if (v_showInfo_4328_ == 0)
{
lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_4326_);
v___x_4414_ = lean_name_append_after(v_attrName_4326_, v___x_4413_);
v___y_4383_ = v___x_4414_;
goto v___jp_4382_;
}
else
{
lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_4326_);
v___x_4416_ = lean_name_append_after(v_attrName_4326_, v___x_4415_);
v___y_4383_ = v___x_4416_;
goto v___jp_4382_;
}
}
v___jp_4338_:
{
lean_object* v___x_4341_; uint8_t v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; uint8_t v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_4342_ = 1;
v___x_4343_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4326_, v___x_4342_);
v___x_4344_ = lean_string_append(v___x_4341_, v___x_4343_);
v___x_4345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_4346_ = lean_string_append(v___x_4344_, v___x_4345_);
v___x_4347_ = lean_string_append(v___x_4346_, v___x_4343_);
v___x_4348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_4349_ = lean_string_append(v___x_4347_, v___x_4348_);
v___x_4350_ = lean_string_append(v___x_4349_, v___x_4343_);
v___x_4351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_4352_ = lean_string_append(v___x_4350_, v___x_4351_);
v___x_4353_ = lean_string_append(v___x_4352_, v___x_4343_);
v___x_4354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_4355_ = lean_string_append(v___x_4353_, v___x_4354_);
v___x_4356_ = lean_string_append(v___x_4355_, v___x_4343_);
v___x_4357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_4358_ = lean_string_append(v___x_4356_, v___x_4357_);
v___x_4359_ = lean_string_append(v___x_4358_, v___x_4343_);
v___x_4360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_4361_ = lean_string_append(v___x_4359_, v___x_4360_);
v___x_4362_ = lean_string_append(v___x_4361_, v___x_4343_);
v___x_4363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_4364_ = lean_string_append(v___x_4362_, v___x_4363_);
v___x_4365_ = lean_string_append(v___x_4364_, v___x_4343_);
v___x_4366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_4367_ = lean_string_append(v___x_4365_, v___x_4366_);
v___x_4368_ = lean_string_append(v___x_4367_, v___x_4343_);
v___x_4369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_4370_ = lean_string_append(v___x_4368_, v___x_4369_);
v___x_4371_ = lean_string_append(v___x_4370_, v___x_4343_);
v___x_4372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_4373_ = lean_string_append(v___x_4371_, v___x_4372_);
v___x_4374_ = lean_string_append(v___x_4373_, v___x_4343_);
lean_dec_ref(v___x_4343_);
v___x_4375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_4376_ = lean_string_append(v___x_4374_, v___x_4375_);
v___x_4377_ = lean_string_append(v___y_4340_, v___x_4376_);
lean_dec_ref(v___x_4376_);
v___x_4378_ = 1;
v___x_4379_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4379_, 0, v_ref_4330_);
lean_ctor_set(v___x_4379_, 1, v___y_4339_);
lean_ctor_set(v___x_4379_, 2, v___x_4377_);
lean_ctor_set_uint8(v___x_4379_, sizeof(void*)*3, v___x_4378_);
v___x_4380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
lean_ctor_set(v___x_4380_, 1, v___f_4337_);
lean_ctor_set(v___x_4380_, 2, v___f_4334_);
v___x_4381_ = l_Lean_registerBuiltinAttribute(v___x_4380_);
return v___x_4381_;
}
v___jp_4382_:
{
if (v_minIndexable_4327_ == 0)
{
if (v_showInfo_4328_ == 0)
{
lean_object* v___x_4384_; uint8_t v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_4385_ = 1;
lean_inc(v_attrName_4326_);
v___x_4386_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4326_, v___x_4385_);
v___x_4387_ = lean_string_append(v___x_4384_, v___x_4386_);
lean_dec_ref(v___x_4386_);
v___x_4388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_4389_ = lean_string_append(v___x_4387_, v___x_4388_);
v___y_4339_ = v___y_4383_;
v___y_4340_ = v___x_4389_;
goto v___jp_4338_;
}
else
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4326_);
v___x_4391_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4326_, v_showInfo_4328_);
v___x_4392_ = lean_string_append(v___x_4390_, v___x_4391_);
v___x_4393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_4394_ = lean_string_append(v___x_4392_, v___x_4393_);
v___x_4395_ = lean_string_append(v___x_4394_, v___x_4391_);
lean_dec_ref(v___x_4391_);
v___x_4396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_4397_ = lean_string_append(v___x_4395_, v___x_4396_);
v___y_4339_ = v___y_4383_;
v___y_4340_ = v___x_4397_;
goto v___jp_4338_;
}
}
else
{
if (v_showInfo_4328_ == 0)
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4326_);
v___x_4399_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4326_, v_minIndexable_4327_);
v___x_4400_ = lean_string_append(v___x_4398_, v___x_4399_);
lean_dec_ref(v___x_4399_);
v___x_4401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_4402_ = lean_string_append(v___x_4400_, v___x_4401_);
v___y_4339_ = v___y_4383_;
v___y_4340_ = v___x_4402_;
goto v___jp_4338_;
}
else
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4326_);
v___x_4404_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4326_, v_showInfo_4328_);
v___x_4405_ = lean_string_append(v___x_4403_, v___x_4404_);
v___x_4406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_4407_ = lean_string_append(v___x_4405_, v___x_4406_);
v___x_4408_ = lean_string_append(v___x_4407_, v___x_4404_);
lean_dec_ref(v___x_4404_);
v___x_4409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_4410_ = lean_string_append(v___x_4408_, v___x_4409_);
v___y_4339_ = v___y_4383_;
v___y_4340_ = v___x_4410_;
goto v___jp_4338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_4417_, lean_object* v_minIndexable_4418_, lean_object* v_showInfo_4419_, lean_object* v_ext_4420_, lean_object* v_ref_4421_, lean_object* v_a_4422_){
_start:
{
uint8_t v_minIndexable_boxed_4423_; uint8_t v_showInfo_boxed_4424_; lean_object* v_res_4425_; 
v_minIndexable_boxed_4423_ = lean_unbox(v_minIndexable_4418_);
v_showInfo_boxed_4424_ = lean_unbox(v_showInfo_4419_);
v_res_4425_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4417_, v_minIndexable_boxed_4423_, v_showInfo_boxed_4424_, v_ext_4420_, v_ref_4421_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_4426_, lean_object* v_msg_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_){
_start:
{
lean_object* v___x_4433_; 
v___x_4433_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_4434_, lean_object* v_msg_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_4434_, v_msg_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_4442_, uint8_t v_attrKind_4443_, uint8_t v_showInfo_4444_, uint8_t v_minIndexable_4445_, lean_object* v_as_4446_, lean_object* v_as_x27_4447_, lean_object* v_b_4448_, lean_object* v_a_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v___x_4455_; 
v___x_4455_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_4442_, v_attrKind_4443_, v_showInfo_4444_, v_minIndexable_4445_, v_as_x27_4447_, v_b_4448_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_4456_, lean_object* v_attrKind_4457_, lean_object* v_showInfo_4458_, lean_object* v_minIndexable_4459_, lean_object* v_as_4460_, lean_object* v_as_x27_4461_, lean_object* v_b_4462_, lean_object* v_a_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
uint8_t v_attrKind_boxed_4469_; uint8_t v_showInfo_boxed_4470_; uint8_t v_minIndexable_boxed_4471_; lean_object* v_res_4472_; 
v_attrKind_boxed_4469_ = lean_unbox(v_attrKind_4457_);
v_showInfo_boxed_4470_ = lean_unbox(v_showInfo_4458_);
v_minIndexable_boxed_4471_ = lean_unbox(v_minIndexable_4459_);
v_res_4472_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_4456_, v_attrKind_boxed_4469_, v_showInfo_boxed_4470_, v_minIndexable_boxed_4471_, v_as_4460_, v_as_x27_4461_, v_b_4462_, v_a_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v_as_x27_4461_);
lean_dec(v_as_4460_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_4473_, lean_object* v_x_4474_, uint8_t v_when_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_4474_, v_when_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_4482_, lean_object* v_x_4483_, lean_object* v_when_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
uint8_t v_when_boxed_4490_; lean_object* v_res_4491_; 
v_when_boxed_4490_ = lean_unbox(v_when_4484_);
v_res_4491_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_4482_, v_x_4483_, v_when_boxed_4490_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v_00_u03b2_4492_, lean_object* v_m_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v___x_4495_; 
v___x_4495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v_m_4493_, v_a_4494_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4496_, lean_object* v_m_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_00_u03b2_4496_, v_m_4497_, v_a_4498_);
lean_dec(v_a_4498_);
lean_dec_ref(v_m_4497_);
return v_res_4499_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_4500_, lean_object* v_x_4501_, lean_object* v_x_4502_){
_start:
{
uint8_t v___x_4503_; 
v___x_4503_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v_x_4501_, v_x_4502_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4504_, lean_object* v_x_4505_, lean_object* v_x_4506_){
_start:
{
uint8_t v_res_4507_; lean_object* v_r_4508_; 
v_res_4507_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(v_00_u03b2_4504_, v_x_4505_, v_x_4506_);
lean_dec_ref(v_x_4506_);
lean_dec_ref(v_x_4505_);
v_r_4508_ = lean_box(v_res_4507_);
return v_r_4508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4509_, lean_object* v_a_4510_, lean_object* v_x_4511_){
_start:
{
lean_object* v___x_4512_; 
v___x_4512_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4510_, v_x_4511_);
return v___x_4512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4513_, lean_object* v_a_4514_, lean_object* v_x_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(v_00_u03b2_4513_, v_a_4514_, v_x_4515_);
lean_dec(v_x_4515_);
lean_dec(v_a_4514_);
return v_res_4516_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4517_, lean_object* v_x_4518_, size_t v_x_4519_, lean_object* v_x_4520_){
_start:
{
uint8_t v___x_4521_; 
v___x_4521_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_4518_, v_x_4519_, v_x_4520_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4522_, lean_object* v_x_4523_, lean_object* v_x_4524_, lean_object* v_x_4525_){
_start:
{
size_t v_x_13060__boxed_4526_; uint8_t v_res_4527_; lean_object* v_r_4528_; 
v_x_13060__boxed_4526_ = lean_unbox_usize(v_x_4524_);
lean_dec(v_x_4524_);
v_res_4527_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(v_00_u03b2_4522_, v_x_4523_, v_x_13060__boxed_4526_, v_x_4525_);
lean_dec_ref(v_x_4525_);
lean_dec_ref(v_x_4523_);
v_r_4528_ = lean_box(v_res_4527_);
return v_r_4528_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_4529_, lean_object* v_keys_4530_, lean_object* v_vals_4531_, lean_object* v_heq_4532_, lean_object* v_i_4533_, lean_object* v_k_4534_){
_start:
{
uint8_t v___x_4535_; 
v___x_4535_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_keys_4530_, v_i_4533_, v_k_4534_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_4536_, lean_object* v_keys_4537_, lean_object* v_vals_4538_, lean_object* v_heq_4539_, lean_object* v_i_4540_, lean_object* v_k_4541_){
_start:
{
uint8_t v_res_4542_; lean_object* v_r_4543_; 
v_res_4542_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(v_00_u03b2_4536_, v_keys_4537_, v_vals_4538_, v_heq_4539_, v_i_4540_, v_k_4541_);
lean_dec_ref(v_k_4541_);
lean_dec_ref(v_vals_4538_);
lean_dec_ref(v_keys_4537_);
v_r_4543_ = lean_box(v_res_4542_);
return v_r_4543_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4544_ = lean_box(0);
v___x_4545_ = lean_unsigned_to_nat(16u);
v___x_4546_ = lean_mk_array(v___x_4545_, v___x_4544_);
return v___x_4546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_4548_ = lean_unsigned_to_nat(0u);
v___x_4549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
lean_ctor_set(v___x_4549_, 1, v___x_4547_);
return v___x_4549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_4552_ = lean_st_mk_ref(v___x_4551_);
v___x_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_4556_, lean_object* v_msg_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v_ref_4561_; lean_object* v___x_4562_; lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4608_; 
v_ref_4561_ = lean_ctor_get(v___y_4558_, 2);
v___x_4562_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_4557_, v___y_4558_, v___y_4559_);
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4565_ = v___x_4562_;
v_isShared_4566_ = v_isSharedCheck_4608_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4562_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4608_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4567_; lean_object* v_traceState_4568_; lean_object* v_env_4569_; lean_object* v_nextMacroScope_4570_; lean_object* v_ngen_4571_; lean_object* v_auxDeclNGen_4572_; lean_object* v_cache_4573_; lean_object* v_recordedDeps_4574_; lean_object* v_messages_4575_; lean_object* v_infoState_4576_; lean_object* v_snapshotTasks_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4607_; 
v___x_4567_ = lean_st_ref_take(v___y_4559_);
v_traceState_4568_ = lean_ctor_get(v___x_4567_, 4);
v_env_4569_ = lean_ctor_get(v___x_4567_, 0);
v_nextMacroScope_4570_ = lean_ctor_get(v___x_4567_, 1);
v_ngen_4571_ = lean_ctor_get(v___x_4567_, 2);
v_auxDeclNGen_4572_ = lean_ctor_get(v___x_4567_, 3);
v_cache_4573_ = lean_ctor_get(v___x_4567_, 5);
v_recordedDeps_4574_ = lean_ctor_get(v___x_4567_, 6);
v_messages_4575_ = lean_ctor_get(v___x_4567_, 7);
v_infoState_4576_ = lean_ctor_get(v___x_4567_, 8);
v_snapshotTasks_4577_ = lean_ctor_get(v___x_4567_, 9);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4579_ = v___x_4567_;
v_isShared_4580_ = v_isSharedCheck_4607_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_snapshotTasks_4577_);
lean_inc(v_infoState_4576_);
lean_inc(v_messages_4575_);
lean_inc(v_recordedDeps_4574_);
lean_inc(v_cache_4573_);
lean_inc(v_traceState_4568_);
lean_inc(v_auxDeclNGen_4572_);
lean_inc(v_ngen_4571_);
lean_inc(v_nextMacroScope_4570_);
lean_inc(v_env_4569_);
lean_dec(v___x_4567_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4607_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
uint64_t v_tid_4581_; lean_object* v_traces_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4606_; 
v_tid_4581_ = lean_ctor_get_uint64(v_traceState_4568_, sizeof(void*)*1);
v_traces_4582_ = lean_ctor_get(v_traceState_4568_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v_traceState_4568_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4584_ = v_traceState_4568_;
v_isShared_4585_ = v_isSharedCheck_4606_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_traces_4582_);
lean_dec(v_traceState_4568_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4606_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; double v___x_4588_; uint8_t v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4597_; 
v___x_4586_ = lean_box(0);
v___x_4587_ = lean_box(0);
v___x_4588_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0);
v___x_4589_ = 0;
v___x_4590_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_4591_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4591_, 0, v_cls_4556_);
lean_ctor_set(v___x_4591_, 1, v___x_4587_);
lean_ctor_set(v___x_4591_, 2, v___x_4590_);
lean_ctor_set_float(v___x_4591_, sizeof(void*)*3, v___x_4588_);
lean_ctor_set_float(v___x_4591_, sizeof(void*)*3 + 8, v___x_4588_);
lean_ctor_set_uint8(v___x_4591_, sizeof(void*)*3 + 16, v___x_4589_);
v___x_4592_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2));
v___x_4593_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4591_);
lean_ctor_set(v___x_4593_, 1, v_a_4563_);
lean_ctor_set(v___x_4593_, 2, v___x_4592_);
lean_inc(v_ref_4561_);
v___x_4594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4594_, 0, v_ref_4561_);
lean_ctor_set(v___x_4594_, 1, v___x_4593_);
v___x_4595_ = l_Lean_PersistentArray_push___redArg(v_traces_4582_, v___x_4594_);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v___x_4595_);
v___x_4597_ = v___x_4584_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4595_);
lean_ctor_set_uint64(v_reuseFailAlloc_4605_, sizeof(void*)*1, v_tid_4581_);
v___x_4597_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
lean_object* v___x_4599_; 
if (v_isShared_4580_ == 0)
{
lean_ctor_set(v___x_4579_, 4, v___x_4597_);
v___x_4599_ = v___x_4579_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_env_4569_);
lean_ctor_set(v_reuseFailAlloc_4604_, 1, v_nextMacroScope_4570_);
lean_ctor_set(v_reuseFailAlloc_4604_, 2, v_ngen_4571_);
lean_ctor_set(v_reuseFailAlloc_4604_, 3, v_auxDeclNGen_4572_);
lean_ctor_set(v_reuseFailAlloc_4604_, 4, v___x_4597_);
lean_ctor_set(v_reuseFailAlloc_4604_, 5, v_cache_4573_);
lean_ctor_set(v_reuseFailAlloc_4604_, 6, v_recordedDeps_4574_);
lean_ctor_set(v_reuseFailAlloc_4604_, 7, v_messages_4575_);
lean_ctor_set(v_reuseFailAlloc_4604_, 8, v_infoState_4576_);
lean_ctor_set(v_reuseFailAlloc_4604_, 9, v_snapshotTasks_4577_);
v___x_4599_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
lean_object* v___x_4600_; lean_object* v___x_4602_; 
v___x_4600_ = lean_st_ref_put(v___y_4559_, v___x_4599_);
if (v_isShared_4566_ == 0)
{
lean_ctor_set(v___x_4565_, 0, v___x_4586_);
v___x_4602_ = v___x_4565_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4586_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_4609_, lean_object* v_msg_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
lean_object* v_res_4614_; 
v_res_4614_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_4609_, v_msg_4610_, v___y_4611_, v___y_4612_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_4615_, uint8_t v_isMeta_4616_, lean_object* v_hint_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
lean_object* v___y_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v_env_4639_; uint8_t v_isExporting_4640_; lean_object* v_entry_4641_; lean_object* v___x_4642_; lean_object* v_env_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; uint8_t v___x_4648_; 
v___x_4637_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0);
v___x_4638_ = lean_st_ref_get(v___y_4619_);
v_env_4639_ = lean_ctor_get(v___x_4638_, 0);
lean_inc_ref(v_env_4639_);
lean_dec(v___x_4638_);
v_isExporting_4640_ = lean_ctor_get_uint8(v_env_4639_, sizeof(void*)*13);
lean_dec_ref(v_env_4639_);
lean_inc(v_mod_4615_);
v_entry_4641_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_4641_, 0, v_mod_4615_);
lean_ctor_set_uint8(v_entry_4641_, sizeof(void*)*1, v_isExporting_4640_);
lean_ctor_set_uint8(v_entry_4641_, sizeof(void*)*1 + 1, v_isMeta_4616_);
v___x_4642_ = lean_st_ref_get(v___y_4619_);
v_env_4643_ = lean_ctor_get(v___x_4642_, 0);
lean_inc_ref(v_env_4643_);
lean_dec(v___x_4642_);
v___x_4644_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_4645_ = lean_box(1);
v___x_4646_ = lean_box(0);
v___x_4647_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4637_, v___x_4644_, v_env_4643_, v___x_4645_, v___x_4646_);
v___x_4648_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v___x_4647_, v_entry_4641_);
lean_dec(v___x_4647_);
if (v___x_4648_ == 0)
{
lean_object* v_toCold_4649_; lean_object* v_options_4650_; lean_object* v_inheritedTraceOptions_4651_; uint8_t v_hasTrace_4652_; lean_object* v___f_4653_; uint8_t v___x_4654_; lean_object* v___y_4656_; 
v_toCold_4649_ = lean_ctor_get(v___y_4618_, 0);
v_options_4650_ = lean_ctor_get(v_toCold_4649_, 2);
v_inheritedTraceOptions_4651_ = lean_ctor_get(v_toCold_4649_, 11);
v_hasTrace_4652_ = lean_ctor_get_uint8(v_options_4650_, sizeof(void*)*1);
v___f_4653_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_4653_, 0, v___x_4644_);
lean_closure_set(v___f_4653_, 1, v_entry_4641_);
v___x_4654_ = 1;
if (v_hasTrace_4652_ == 0)
{
lean_dec(v_hint_4617_);
lean_dec(v_mod_4615_);
v___y_4656_ = v___y_4619_;
goto v___jp_4655_;
}
else
{
lean_object* v_cls_4674_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v___x_4694_; uint8_t v___x_4695_; 
v_cls_4674_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_4694_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8);
v___x_4695_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4651_, v_options_4650_, v___x_4694_);
if (v___x_4695_ == 0)
{
lean_dec(v_hint_4617_);
lean_dec(v_mod_4615_);
v___y_4656_ = v___y_4619_;
goto v___jp_4655_;
}
else
{
lean_object* v___x_4696_; lean_object* v___y_4698_; 
v___x_4696_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10);
if (v_isExporting_4640_ == 0)
{
lean_object* v___x_4705_; 
v___x_4705_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15));
v___y_4698_ = v___x_4705_;
goto v___jp_4697_;
}
else
{
lean_object* v___x_4706_; 
v___x_4706_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16));
v___y_4698_ = v___x_4706_;
goto v___jp_4697_;
}
v___jp_4697_:
{
lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; 
lean_inc_ref(v___y_4698_);
v___x_4699_ = l_Lean_stringToMessageData(v___y_4698_);
v___x_4700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4696_);
lean_ctor_set(v___x_4700_, 1, v___x_4699_);
v___x_4701_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12);
v___x_4702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4702_, 0, v___x_4700_);
lean_ctor_set(v___x_4702_, 1, v___x_4701_);
if (v_isMeta_4616_ == 0)
{
lean_object* v___x_4703_; 
v___x_4703_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13));
v___y_4681_ = v___x_4702_;
v___y_4682_ = v___x_4703_;
goto v___jp_4680_;
}
else
{
lean_object* v___x_4704_; 
v___x_4704_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14));
v___y_4681_ = v___x_4702_;
v___y_4682_ = v___x_4704_;
goto v___jp_4680_;
}
}
}
v___jp_4675_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4678_, 0, v___y_4676_);
lean_ctor_set(v___x_4678_, 1, v___y_4677_);
v___x_4679_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_4674_, v___x_4678_, v___y_4618_, v___y_4619_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_dec_ref_known(v___x_4679_, 1);
v___y_4656_ = v___y_4619_;
goto v___jp_4655_;
}
else
{
lean_dec_ref(v___f_4653_);
return v___x_4679_;
}
}
v___jp_4680_:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; uint8_t v___x_4689_; 
lean_inc_ref(v___y_4682_);
v___x_4683_ = l_Lean_stringToMessageData(v___y_4682_);
v___x_4684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4684_, 0, v___y_4681_);
lean_ctor_set(v___x_4684_, 1, v___x_4683_);
v___x_4685_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4);
v___x_4686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4684_);
lean_ctor_set(v___x_4686_, 1, v___x_4685_);
v___x_4687_ = l_Lean_MessageData_ofName(v_mod_4615_);
v___x_4688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4686_);
lean_ctor_set(v___x_4688_, 1, v___x_4687_);
v___x_4689_ = l_Lean_Name_isAnonymous(v_hint_4617_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4690_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6);
v___x_4691_ = l_Lean_MessageData_ofName(v_hint_4617_);
v___x_4692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4690_);
lean_ctor_set(v___x_4692_, 1, v___x_4691_);
v___y_4676_ = v___x_4688_;
v___y_4677_ = v___x_4692_;
goto v___jp_4675_;
}
else
{
lean_object* v___x_4693_; 
lean_dec(v_hint_4617_);
v___x_4693_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7);
v___y_4676_ = v___x_4688_;
v___y_4677_ = v___x_4693_;
goto v___jp_4675_;
}
}
}
v___jp_4655_:
{
lean_object* v___x_4657_; lean_object* v_toEnvExtension_4658_; lean_object* v_env_4659_; lean_object* v_nextMacroScope_4660_; lean_object* v_ngen_4661_; lean_object* v_auxDeclNGen_4662_; lean_object* v_traceState_4663_; lean_object* v_recordedDeps_4664_; lean_object* v_messages_4665_; lean_object* v_infoState_4666_; lean_object* v_snapshotTasks_4667_; lean_object* v_asyncMode_4668_; uint8_t v_logWrites_4669_; lean_object* v___x_4670_; 
v___x_4657_ = lean_st_ref_take(v___y_4656_);
v_toEnvExtension_4658_ = lean_ctor_get(v___x_4644_, 0);
v_env_4659_ = lean_ctor_get(v___x_4657_, 0);
lean_inc_ref(v_env_4659_);
v_nextMacroScope_4660_ = lean_ctor_get(v___x_4657_, 1);
lean_inc(v_nextMacroScope_4660_);
v_ngen_4661_ = lean_ctor_get(v___x_4657_, 2);
lean_inc_ref(v_ngen_4661_);
v_auxDeclNGen_4662_ = lean_ctor_get(v___x_4657_, 3);
lean_inc_ref(v_auxDeclNGen_4662_);
v_traceState_4663_ = lean_ctor_get(v___x_4657_, 4);
lean_inc_ref(v_traceState_4663_);
v_recordedDeps_4664_ = lean_ctor_get(v___x_4657_, 6);
lean_inc_ref(v_recordedDeps_4664_);
v_messages_4665_ = lean_ctor_get(v___x_4657_, 7);
lean_inc_ref(v_messages_4665_);
v_infoState_4666_ = lean_ctor_get(v___x_4657_, 8);
lean_inc_ref(v_infoState_4666_);
v_snapshotTasks_4667_ = lean_ctor_get(v___x_4657_, 9);
lean_inc_ref(v_snapshotTasks_4667_);
lean_dec(v___x_4657_);
v_asyncMode_4668_ = lean_ctor_get(v_toEnvExtension_4658_, 2);
v_logWrites_4669_ = lean_ctor_get_uint8(v_toEnvExtension_4658_, sizeof(void*)*6);
v___x_4670_ = lean_box(0);
if (v_logWrites_4669_ == 0)
{
lean_object* v___x_4671_; 
lean_inc_ref(v_toEnvExtension_4658_);
v___x_4671_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4658_, v_env_4659_, v___f_4653_, v_asyncMode_4668_, v___x_4646_, v___x_4654_);
v___y_4622_ = v_ngen_4661_;
v___y_4623_ = v_auxDeclNGen_4662_;
v___y_4624_ = v_traceState_4663_;
v___y_4625_ = v___y_4656_;
v___y_4626_ = v_nextMacroScope_4660_;
v___y_4627_ = v_infoState_4666_;
v___y_4628_ = v_messages_4665_;
v___y_4629_ = v___x_4670_;
v___y_4630_ = v_snapshotTasks_4667_;
v___y_4631_ = v_recordedDeps_4664_;
v___y_4632_ = v___x_4671_;
goto v___jp_4621_;
}
else
{
lean_object* v___x_4672_; lean_object* v___x_4673_; 
lean_inc_ref_n(v_toEnvExtension_4658_, 2);
v___x_4672_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4658_, v_env_4659_);
lean_dec_ref(v_env_4659_);
v___x_4673_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4658_, v___x_4672_, v___f_4653_, v_asyncMode_4668_, v___x_4646_, v___x_4654_);
v___y_4622_ = v_ngen_4661_;
v___y_4623_ = v_auxDeclNGen_4662_;
v___y_4624_ = v_traceState_4663_;
v___y_4625_ = v___y_4656_;
v___y_4626_ = v_nextMacroScope_4660_;
v___y_4627_ = v_infoState_4666_;
v___y_4628_ = v_messages_4665_;
v___y_4629_ = v___x_4670_;
v___y_4630_ = v_snapshotTasks_4667_;
v___y_4631_ = v_recordedDeps_4664_;
v___y_4632_ = v___x_4673_;
goto v___jp_4621_;
}
}
}
else
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
lean_dec_ref_known(v_entry_4641_, 1);
lean_dec(v_hint_4617_);
lean_dec(v_mod_4615_);
v___x_4707_ = lean_box(0);
v___x_4708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4708_, 0, v___x_4707_);
return v___x_4708_;
}
v___jp_4621_:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4633_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
v___x_4634_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4634_, 0, v___y_4632_);
lean_ctor_set(v___x_4634_, 1, v___y_4626_);
lean_ctor_set(v___x_4634_, 2, v___y_4622_);
lean_ctor_set(v___x_4634_, 3, v___y_4623_);
lean_ctor_set(v___x_4634_, 4, v___y_4624_);
lean_ctor_set(v___x_4634_, 5, v___x_4633_);
lean_ctor_set(v___x_4634_, 6, v___y_4631_);
lean_ctor_set(v___x_4634_, 7, v___y_4628_);
lean_ctor_set(v___x_4634_, 8, v___y_4627_);
lean_ctor_set(v___x_4634_, 9, v___y_4630_);
v___x_4635_ = lean_st_ref_put(v___y_4625_, v___x_4634_);
v___x_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___y_4629_);
return v___x_4636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_4709_, lean_object* v_isMeta_4710_, lean_object* v_hint_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_){
_start:
{
uint8_t v_isMeta_boxed_4715_; lean_object* v_res_4716_; 
v_isMeta_boxed_4715_ = lean_unbox(v_isMeta_4710_);
v_res_4716_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_4709_, v_isMeta_boxed_4715_, v_hint_4711_, v___y_4712_, v___y_4713_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_4717_, lean_object* v_declName_4718_, lean_object* v_as_4719_, size_t v_sz_4720_, size_t v_i_4721_, lean_object* v_b_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
uint8_t v___x_4726_; 
v___x_4726_ = lean_usize_dec_lt(v_i_4721_, v_sz_4720_);
if (v___x_4726_ == 0)
{
lean_object* v___x_4727_; 
lean_dec(v_declName_4718_);
v___x_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4727_, 0, v_b_4722_);
return v___x_4727_;
}
else
{
lean_object* v___x_4728_; lean_object* v_modules_4729_; lean_object* v___x_4730_; lean_object* v_a_4731_; lean_object* v___x_4732_; lean_object* v_toImport_4733_; lean_object* v_module_4734_; lean_object* v___x_4735_; uint8_t v___x_4736_; lean_object* v___x_4737_; 
v___x_4728_ = l_Lean_Environment_header(v___x_4717_);
v_modules_4729_ = lean_ctor_get(v___x_4728_, 3);
lean_inc_ref(v_modules_4729_);
lean_dec_ref(v___x_4728_);
v___x_4730_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_4731_ = lean_array_uget_borrowed(v_as_4719_, v_i_4721_);
v___x_4732_ = lean_array_get(v___x_4730_, v_modules_4729_, v_a_4731_);
lean_dec_ref(v_modules_4729_);
v_toImport_4733_ = lean_ctor_get(v___x_4732_, 0);
lean_inc_ref(v_toImport_4733_);
lean_dec(v___x_4732_);
v_module_4734_ = lean_ctor_get(v_toImport_4733_, 0);
lean_inc(v_module_4734_);
lean_dec_ref(v_toImport_4733_);
v___x_4735_ = lean_box(0);
v___x_4736_ = 0;
lean_inc(v_declName_4718_);
v___x_4737_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_4734_, v___x_4736_, v_declName_4718_, v___y_4723_, v___y_4724_);
if (lean_obj_tag(v___x_4737_) == 0)
{
size_t v___x_4738_; size_t v___x_4739_; 
lean_dec_ref_known(v___x_4737_, 1);
v___x_4738_ = ((size_t)1ULL);
v___x_4739_ = lean_usize_add(v_i_4721_, v___x_4738_);
v_i_4721_ = v___x_4739_;
v_b_4722_ = v___x_4735_;
goto _start;
}
else
{
lean_dec(v_declName_4718_);
return v___x_4737_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_4741_, lean_object* v_declName_4742_, lean_object* v_as_4743_, lean_object* v_sz_4744_, lean_object* v_i_4745_, lean_object* v_b_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_){
_start:
{
size_t v_sz_boxed_4750_; size_t v_i_boxed_4751_; lean_object* v_res_4752_; 
v_sz_boxed_4750_ = lean_unbox_usize(v_sz_4744_);
lean_dec(v_sz_4744_);
v_i_boxed_4751_ = lean_unbox_usize(v_i_4745_);
lean_dec(v_i_4745_);
v_res_4752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_4741_, v_declName_4742_, v_as_4743_, v_sz_boxed_4750_, v_i_boxed_4751_, v_b_4746_, v___y_4747_, v___y_4748_);
lean_dec(v___y_4748_);
lean_dec_ref(v___y_4747_);
lean_dec_ref(v_as_4743_);
lean_dec_ref(v___x_4741_);
return v_res_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_4753_, uint8_t v_isMeta_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_){
_start:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v_env_4763_; lean_object* v___y_4765_; lean_object* v___x_4778_; 
v___x_4758_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_4759_ = lean_st_ref_get(v___y_4756_);
v_env_4763_ = lean_ctor_get(v___x_4759_, 0);
lean_inc_ref(v_env_4763_);
lean_dec(v___x_4759_);
v___x_4778_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4763_, v_declName_4753_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_dec_ref(v_env_4763_);
lean_dec(v_declName_4753_);
goto v___jp_4760_;
}
else
{
lean_object* v_val_4779_; lean_object* v___x_4780_; lean_object* v_modules_4781_; lean_object* v___x_4782_; uint8_t v___x_4783_; 
v_val_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_val_4779_);
lean_dec_ref_known(v___x_4778_, 1);
v___x_4780_ = l_Lean_Environment_header(v_env_4763_);
v_modules_4781_ = lean_ctor_get(v___x_4780_, 3);
lean_inc_ref(v_modules_4781_);
lean_dec_ref(v___x_4780_);
v___x_4782_ = lean_array_get_size(v_modules_4781_);
v___x_4783_ = lean_nat_dec_lt(v_val_4779_, v___x_4782_);
if (v___x_4783_ == 0)
{
lean_dec_ref(v_modules_4781_);
lean_dec(v_val_4779_);
lean_dec_ref(v_env_4763_);
lean_dec(v_declName_4753_);
goto v___jp_4760_;
}
else
{
lean_object* v___x_4784_; lean_object* v___x_4785_; uint8_t v___y_4787_; 
v___x_4784_ = lean_array_fget(v_modules_4781_, v_val_4779_);
lean_dec(v_val_4779_);
lean_dec_ref(v_modules_4781_);
v___x_4785_ = lean_st_ref_get(v___y_4756_);
if (v_isMeta_4754_ == 0)
{
lean_dec(v___x_4785_);
v___y_4787_ = v_isMeta_4754_;
goto v___jp_4786_;
}
else
{
lean_object* v_env_4798_; uint8_t v___x_4799_; 
v_env_4798_ = lean_ctor_get(v___x_4785_, 0);
lean_inc_ref(v_env_4798_);
lean_dec(v___x_4785_);
lean_inc(v_declName_4753_);
v___x_4799_ = l_Lean_isMarkedMeta(v_env_4798_, v_declName_4753_);
if (v___x_4799_ == 0)
{
v___y_4787_ = v_isMeta_4754_;
goto v___jp_4786_;
}
else
{
uint8_t v___x_4800_; 
v___x_4800_ = 0;
v___y_4787_ = v___x_4800_;
goto v___jp_4786_;
}
}
v___jp_4786_:
{
lean_object* v_toImport_4788_; lean_object* v_module_4789_; lean_object* v___x_4790_; 
v_toImport_4788_ = lean_ctor_get(v___x_4784_, 0);
lean_inc_ref(v_toImport_4788_);
lean_dec(v___x_4784_);
v_module_4789_ = lean_ctor_get(v_toImport_4788_, 0);
lean_inc(v_module_4789_);
lean_dec_ref(v_toImport_4788_);
lean_inc(v_declName_4753_);
v___x_4790_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_4789_, v___y_4787_, v_declName_4753_, v___y_4755_, v___y_4756_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
lean_dec_ref_known(v___x_4790_, 1);
v___x_4791_ = l_Lean_indirectModUseExt;
v___x_4792_ = lean_box(1);
v___x_4793_ = lean_box(0);
lean_inc_ref(v_env_4763_);
v___x_4794_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4758_, v___x_4791_, v_env_4763_, v___x_4792_, v___x_4793_);
v___x_4795_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4794_, v_declName_4753_);
lean_dec(v___x_4794_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v___x_4796_; 
v___x_4796_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_4765_ = v___x_4796_;
goto v___jp_4764_;
}
else
{
lean_object* v_val_4797_; 
v_val_4797_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_val_4797_);
lean_dec_ref_known(v___x_4795_, 1);
v___y_4765_ = v_val_4797_;
goto v___jp_4764_;
}
}
else
{
lean_dec_ref(v_env_4763_);
lean_dec(v_declName_4753_);
return v___x_4790_;
}
}
}
}
v___jp_4760_:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4761_ = lean_box(0);
v___x_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4761_);
return v___x_4762_;
}
v___jp_4764_:
{
lean_object* v___x_4766_; size_t v_sz_4767_; size_t v___x_4768_; lean_object* v___x_4769_; 
v___x_4766_ = lean_box(0);
v_sz_4767_ = lean_array_size(v___y_4765_);
v___x_4768_ = ((size_t)0ULL);
v___x_4769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_4763_, v_declName_4753_, v___y_4765_, v_sz_4767_, v___x_4768_, v___x_4766_, v___y_4755_, v___y_4756_);
lean_dec_ref(v___y_4765_);
lean_dec_ref(v_env_4763_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4776_; 
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4776_ == 0)
{
lean_object* v_unused_4777_; 
v_unused_4777_ = lean_ctor_get(v___x_4769_, 0);
lean_dec(v_unused_4777_);
v___x_4771_ = v___x_4769_;
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
else
{
lean_dec(v___x_4769_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4774_; 
if (v_isShared_4772_ == 0)
{
lean_ctor_set(v___x_4771_, 0, v___x_4766_);
v___x_4774_ = v___x_4771_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4766_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
else
{
return v___x_4769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_4801_, lean_object* v_isMeta_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
uint8_t v_isMeta_boxed_4806_; lean_object* v_res_4807_; 
v_isMeta_boxed_4806_ = lean_unbox(v_isMeta_4802_);
v_res_4807_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_4801_, v_isMeta_boxed_4806_, v___y_4803_, v___y_4804_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v___x_4812_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4813_ = lean_st_ref_get(v___x_4812_);
v___x_4814_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4813_, v_attrName_4808_);
lean_dec(v___x_4813_);
if (lean_obj_tag(v___x_4814_) == 1)
{
lean_object* v_val_4815_; lean_object* v_ext_4816_; lean_object* v_name_4817_; uint8_t v___x_4818_; lean_object* v___x_4819_; 
v_val_4815_ = lean_ctor_get(v___x_4814_, 0);
v_ext_4816_ = lean_ctor_get(v_val_4815_, 1);
v_name_4817_ = lean_ctor_get(v_ext_4816_, 1);
v___x_4818_ = 1;
lean_inc(v_name_4817_);
v___x_4819_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_4817_, v___x_4818_, v_a_4809_, v_a_4810_);
if (lean_obj_tag(v___x_4819_) == 0)
{
lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4826_ == 0)
{
lean_object* v_unused_4827_; 
v_unused_4827_ = lean_ctor_get(v___x_4819_, 0);
lean_dec(v_unused_4827_);
v___x_4821_ = v___x_4819_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_dec(v___x_4819_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 0, v___x_4814_);
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___x_4814_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
lean_dec_ref_known(v___x_4814_, 1);
v_a_4828_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4819_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4819_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
else
{
lean_object* v___x_4836_; 
v___x_4836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4814_);
return v___x_4836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_4837_, v_a_4838_, v_a_4839_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
lean_dec(v_attrName_4837_);
return v_res_4841_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_4842_; 
v___x_4842_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_4843_, lean_object* v_x_4844_){
_start:
{
if (lean_obj_tag(v_x_4844_) == 0)
{
return v_x_4843_;
}
else
{
lean_object* v_key_4845_; lean_object* v_value_4846_; lean_object* v_tail_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4873_; 
v_key_4845_ = lean_ctor_get(v_x_4844_, 0);
v_value_4846_ = lean_ctor_get(v_x_4844_, 1);
v_tail_4847_ = lean_ctor_get(v_x_4844_, 2);
v_isSharedCheck_4873_ = !lean_is_exclusive(v_x_4844_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4849_ = v_x_4844_;
v_isShared_4850_ = v_isSharedCheck_4873_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_tail_4847_);
lean_inc(v_value_4846_);
lean_inc(v_key_4845_);
lean_dec(v_x_4844_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4873_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4851_; uint64_t v___y_4853_; 
v___x_4851_ = lean_array_get_size(v_x_4843_);
if (lean_obj_tag(v_key_4845_) == 0)
{
uint64_t v___x_4871_; 
v___x_4871_ = 1723ULL;
v___y_4853_ = v___x_4871_;
goto v___jp_4852_;
}
else
{
uint64_t v_hash_4872_; 
v_hash_4872_ = lean_ctor_get_uint64(v_key_4845_, sizeof(void*)*2);
v___y_4853_ = v_hash_4872_;
goto v___jp_4852_;
}
v___jp_4852_:
{
uint64_t v___x_4854_; uint64_t v___x_4855_; uint64_t v_fold_4856_; uint64_t v___x_4857_; uint64_t v___x_4858_; uint64_t v___x_4859_; size_t v___x_4860_; size_t v___x_4861_; size_t v___x_4862_; size_t v___x_4863_; size_t v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4867_; 
v___x_4854_ = 32ULL;
v___x_4855_ = lean_uint64_shift_right(v___y_4853_, v___x_4854_);
v_fold_4856_ = lean_uint64_xor(v___y_4853_, v___x_4855_);
v___x_4857_ = 16ULL;
v___x_4858_ = lean_uint64_shift_right(v_fold_4856_, v___x_4857_);
v___x_4859_ = lean_uint64_xor(v_fold_4856_, v___x_4858_);
v___x_4860_ = lean_uint64_to_usize(v___x_4859_);
v___x_4861_ = lean_usize_of_nat(v___x_4851_);
v___x_4862_ = ((size_t)1ULL);
v___x_4863_ = lean_usize_sub(v___x_4861_, v___x_4862_);
v___x_4864_ = lean_usize_land(v___x_4860_, v___x_4863_);
v___x_4865_ = lean_array_uget_borrowed(v_x_4843_, v___x_4864_);
lean_inc(v___x_4865_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 2, v___x_4865_);
v___x_4867_ = v___x_4849_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_key_4845_);
lean_ctor_set(v_reuseFailAlloc_4870_, 1, v_value_4846_);
lean_ctor_set(v_reuseFailAlloc_4870_, 2, v___x_4865_);
v___x_4867_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
lean_object* v___x_4868_; 
v___x_4868_ = lean_array_uset(v_x_4843_, v___x_4864_, v___x_4867_);
v_x_4843_ = v___x_4868_;
v_x_4844_ = v_tail_4847_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_4874_, lean_object* v_source_4875_, lean_object* v_target_4876_){
_start:
{
lean_object* v___x_4877_; uint8_t v___x_4878_; 
v___x_4877_ = lean_array_get_size(v_source_4875_);
v___x_4878_ = lean_nat_dec_lt(v_i_4874_, v___x_4877_);
if (v___x_4878_ == 0)
{
lean_dec_ref(v_source_4875_);
lean_dec(v_i_4874_);
return v_target_4876_;
}
else
{
lean_object* v_es_4879_; lean_object* v___x_4880_; lean_object* v_source_4881_; lean_object* v_target_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
v_es_4879_ = lean_array_fget(v_source_4875_, v_i_4874_);
v___x_4880_ = lean_box(0);
v_source_4881_ = lean_array_fset(v_source_4875_, v_i_4874_, v___x_4880_);
v_target_4882_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_4876_, v_es_4879_);
v___x_4883_ = lean_unsigned_to_nat(1u);
v___x_4884_ = lean_nat_add(v_i_4874_, v___x_4883_);
lean_dec(v_i_4874_);
v_i_4874_ = v___x_4884_;
v_source_4875_ = v_source_4881_;
v_target_4876_ = v_target_4882_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_4886_){
_start:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v_nbuckets_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4887_ = lean_array_get_size(v_data_4886_);
v___x_4888_ = lean_unsigned_to_nat(2u);
v_nbuckets_4889_ = lean_nat_mul(v___x_4887_, v___x_4888_);
v___x_4890_ = lean_unsigned_to_nat(0u);
v___x_4891_ = lean_box(0);
v___x_4892_ = lean_mk_array(v_nbuckets_4889_, v___x_4891_);
v___x_4893_ = lean_array_propagate_mark(v_data_4886_, v___x_4892_);
v___x_4894_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_4890_, v_data_4886_, v___x_4893_);
return v___x_4894_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_4895_, lean_object* v_x_4896_){
_start:
{
if (lean_obj_tag(v_x_4896_) == 0)
{
uint8_t v___x_4897_; 
v___x_4897_ = 0;
return v___x_4897_;
}
else
{
lean_object* v_key_4898_; lean_object* v_tail_4899_; uint8_t v___x_4900_; 
v_key_4898_ = lean_ctor_get(v_x_4896_, 0);
v_tail_4899_ = lean_ctor_get(v_x_4896_, 2);
v___x_4900_ = lean_name_eq(v_key_4898_, v_a_4895_);
if (v___x_4900_ == 0)
{
v_x_4896_ = v_tail_4899_;
goto _start;
}
else
{
return v___x_4900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_4902_, lean_object* v_x_4903_){
_start:
{
uint8_t v_res_4904_; lean_object* v_r_4905_; 
v_res_4904_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4902_, v_x_4903_);
lean_dec(v_x_4903_);
lean_dec(v_a_4902_);
v_r_4905_ = lean_box(v_res_4904_);
return v_r_4905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_4906_, lean_object* v_b_4907_, lean_object* v_x_4908_){
_start:
{
if (lean_obj_tag(v_x_4908_) == 0)
{
lean_dec(v_b_4907_);
lean_dec(v_a_4906_);
return v_x_4908_;
}
else
{
lean_object* v_key_4909_; lean_object* v_value_4910_; lean_object* v_tail_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4923_; 
v_key_4909_ = lean_ctor_get(v_x_4908_, 0);
v_value_4910_ = lean_ctor_get(v_x_4908_, 1);
v_tail_4911_ = lean_ctor_get(v_x_4908_, 2);
v_isSharedCheck_4923_ = !lean_is_exclusive(v_x_4908_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4913_ = v_x_4908_;
v_isShared_4914_ = v_isSharedCheck_4923_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_tail_4911_);
lean_inc(v_value_4910_);
lean_inc(v_key_4909_);
lean_dec(v_x_4908_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4923_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
uint8_t v___x_4915_; 
v___x_4915_ = lean_name_eq(v_key_4909_, v_a_4906_);
if (v___x_4915_ == 0)
{
lean_object* v___x_4916_; lean_object* v___x_4918_; 
v___x_4916_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4906_, v_b_4907_, v_tail_4911_);
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 2, v___x_4916_);
v___x_4918_ = v___x_4913_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_key_4909_);
lean_ctor_set(v_reuseFailAlloc_4919_, 1, v_value_4910_);
lean_ctor_set(v_reuseFailAlloc_4919_, 2, v___x_4916_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
else
{
lean_object* v___x_4921_; 
lean_dec(v_value_4910_);
lean_dec(v_key_4909_);
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 1, v_b_4907_);
lean_ctor_set(v___x_4913_, 0, v_a_4906_);
v___x_4921_ = v___x_4913_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4906_);
lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_b_4907_);
lean_ctor_set(v_reuseFailAlloc_4922_, 2, v_tail_4911_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_4924_, lean_object* v_a_4925_, lean_object* v_b_4926_){
_start:
{
lean_object* v_size_4927_; lean_object* v_buckets_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4974_; 
v_size_4927_ = lean_ctor_get(v_m_4924_, 0);
v_buckets_4928_ = lean_ctor_get(v_m_4924_, 1);
v_isSharedCheck_4974_ = !lean_is_exclusive(v_m_4924_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4930_ = v_m_4924_;
v_isShared_4931_ = v_isSharedCheck_4974_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_buckets_4928_);
lean_inc(v_size_4927_);
lean_dec(v_m_4924_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4974_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4932_; uint64_t v___y_4934_; 
v___x_4932_ = lean_array_get_size(v_buckets_4928_);
if (lean_obj_tag(v_a_4925_) == 0)
{
uint64_t v___x_4972_; 
v___x_4972_ = 1723ULL;
v___y_4934_ = v___x_4972_;
goto v___jp_4933_;
}
else
{
uint64_t v_hash_4973_; 
v_hash_4973_ = lean_ctor_get_uint64(v_a_4925_, sizeof(void*)*2);
v___y_4934_ = v_hash_4973_;
goto v___jp_4933_;
}
v___jp_4933_:
{
uint64_t v___x_4935_; uint64_t v___x_4936_; uint64_t v_fold_4937_; uint64_t v___x_4938_; uint64_t v___x_4939_; uint64_t v___x_4940_; size_t v___x_4941_; size_t v___x_4942_; size_t v___x_4943_; size_t v___x_4944_; size_t v___x_4945_; lean_object* v_bkt_4946_; uint8_t v___x_4947_; 
v___x_4935_ = 32ULL;
v___x_4936_ = lean_uint64_shift_right(v___y_4934_, v___x_4935_);
v_fold_4937_ = lean_uint64_xor(v___y_4934_, v___x_4936_);
v___x_4938_ = 16ULL;
v___x_4939_ = lean_uint64_shift_right(v_fold_4937_, v___x_4938_);
v___x_4940_ = lean_uint64_xor(v_fold_4937_, v___x_4939_);
v___x_4941_ = lean_uint64_to_usize(v___x_4940_);
v___x_4942_ = lean_usize_of_nat(v___x_4932_);
v___x_4943_ = ((size_t)1ULL);
v___x_4944_ = lean_usize_sub(v___x_4942_, v___x_4943_);
v___x_4945_ = lean_usize_land(v___x_4941_, v___x_4944_);
v_bkt_4946_ = lean_array_uget_borrowed(v_buckets_4928_, v___x_4945_);
v___x_4947_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4925_, v_bkt_4946_);
if (v___x_4947_ == 0)
{
lean_object* v___x_4948_; lean_object* v_size_x27_4949_; lean_object* v___x_4950_; lean_object* v_buckets_x27_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; uint8_t v___x_4957_; 
v___x_4948_ = lean_unsigned_to_nat(1u);
v_size_x27_4949_ = lean_nat_add(v_size_4927_, v___x_4948_);
lean_dec(v_size_4927_);
lean_inc(v_bkt_4946_);
v___x_4950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4950_, 0, v_a_4925_);
lean_ctor_set(v___x_4950_, 1, v_b_4926_);
lean_ctor_set(v___x_4950_, 2, v_bkt_4946_);
v_buckets_x27_4951_ = lean_array_uset(v_buckets_4928_, v___x_4945_, v___x_4950_);
v___x_4952_ = lean_unsigned_to_nat(4u);
v___x_4953_ = lean_nat_mul(v_size_x27_4949_, v___x_4952_);
v___x_4954_ = lean_unsigned_to_nat(3u);
v___x_4955_ = lean_nat_div(v___x_4953_, v___x_4954_);
lean_dec(v___x_4953_);
v___x_4956_ = lean_array_get_size(v_buckets_x27_4951_);
v___x_4957_ = lean_nat_dec_le(v___x_4955_, v___x_4956_);
lean_dec(v___x_4955_);
if (v___x_4957_ == 0)
{
lean_object* v_val_4958_; lean_object* v___x_4960_; 
v_val_4958_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_4951_);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 1, v_val_4958_);
lean_ctor_set(v___x_4930_, 0, v_size_x27_4949_);
v___x_4960_ = v___x_4930_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_size_x27_4949_);
lean_ctor_set(v_reuseFailAlloc_4961_, 1, v_val_4958_);
v___x_4960_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
return v___x_4960_;
}
}
else
{
lean_object* v___x_4963_; 
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 1, v_buckets_x27_4951_);
lean_ctor_set(v___x_4930_, 0, v_size_x27_4949_);
v___x_4963_ = v___x_4930_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_size_x27_4949_);
lean_ctor_set(v_reuseFailAlloc_4964_, 1, v_buckets_x27_4951_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
else
{
lean_object* v___x_4965_; lean_object* v_buckets_x27_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4970_; 
lean_inc(v_bkt_4946_);
v___x_4965_ = lean_box(0);
v_buckets_x27_4966_ = lean_array_uset(v_buckets_4928_, v___x_4945_, v___x_4965_);
v___x_4967_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4925_, v_b_4926_, v_bkt_4946_);
v___x_4968_ = lean_array_uset(v_buckets_x27_4966_, v___x_4945_, v___x_4967_);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 1, v___x_4968_);
v___x_4970_ = v___x_4930_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_size_4927_);
lean_ctor_set(v_reuseFailAlloc_4971_, 1, v___x_4968_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_4975_, lean_object* v_ref_4976_){
_start:
{
lean_object* v___x_4978_; 
lean_inc(v_ref_4976_);
v___x_4978_ = l_Lean_Meta_Grind_mkExtension(v_ref_4976_);
if (lean_obj_tag(v___x_4978_) == 0)
{
lean_object* v_a_4979_; uint8_t v___x_4980_; uint8_t v___x_4981_; lean_object* v___x_4982_; 
v_a_4979_ = lean_ctor_get(v___x_4978_, 0);
lean_inc_n(v_a_4979_, 2);
lean_dec_ref_known(v___x_4978_, 1);
v___x_4980_ = 0;
v___x_4981_ = 1;
lean_inc(v_ref_4976_);
lean_inc(v_attrName_4975_);
v___x_4982_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4975_, v___x_4980_, v___x_4981_, v_a_4979_, v_ref_4976_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v___x_4983_; 
lean_dec_ref_known(v___x_4982_, 1);
lean_inc(v_ref_4976_);
lean_inc(v_a_4979_);
lean_inc(v_attrName_4975_);
v___x_4983_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4975_, v___x_4980_, v___x_4980_, v_a_4979_, v_ref_4976_);
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v___x_4984_; 
lean_dec_ref_known(v___x_4983_, 1);
lean_inc(v_ref_4976_);
lean_inc(v_a_4979_);
lean_inc(v_attrName_4975_);
v___x_4984_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4975_, v___x_4981_, v___x_4981_, v_a_4979_, v_ref_4976_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v___x_4985_; 
lean_dec_ref_known(v___x_4984_, 1);
lean_inc(v_a_4979_);
lean_inc(v_attrName_4975_);
v___x_4985_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4975_, v___x_4981_, v___x_4980_, v_a_4979_, v_ref_4976_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_4996_; 
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_4996_ == 0)
{
lean_object* v_unused_4997_; 
v_unused_4997_ = lean_ctor_get(v___x_4985_, 0);
lean_dec(v_unused_4997_);
v___x_4987_ = v___x_4985_;
v_isShared_4988_ = v_isSharedCheck_4996_;
goto v_resetjp_4986_;
}
else
{
lean_dec(v___x_4985_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_4996_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4994_; 
v___x_4989_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4990_ = lean_st_ref_take(v___x_4989_);
lean_inc(v_a_4979_);
v___x_4991_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_4990_, v_attrName_4975_, v_a_4979_);
v___x_4992_ = lean_st_ref_put(v___x_4989_, v___x_4991_);
if (v_isShared_4988_ == 0)
{
lean_ctor_set(v___x_4987_, 0, v_a_4979_);
v___x_4994_ = v___x_4987_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4979_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
lean_dec(v_a_4979_);
lean_dec(v_attrName_4975_);
v_a_4998_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4985_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4985_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_5001_ == 0)
{
v___x_5003_ = v___x_5000_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_a_4998_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
}
}
else
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5013_; 
lean_dec(v_a_4979_);
lean_dec(v_ref_4976_);
lean_dec(v_attrName_4975_);
v_a_5006_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4984_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4984_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_5009_ == 0)
{
v___x_5011_ = v___x_5008_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
}
}
else
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
lean_dec(v_a_4979_);
lean_dec(v_ref_4976_);
lean_dec(v_attrName_4975_);
v_a_5014_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_4983_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_4983_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
lean_dec(v_a_4979_);
lean_dec(v_ref_4976_);
lean_dec(v_attrName_4975_);
v_a_5022_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5024_ = v___x_4982_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_4982_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
}
else
{
lean_dec(v_ref_4976_);
lean_dec(v_attrName_4975_);
return v___x_4978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_5030_, lean_object* v_ref_5031_, lean_object* v_a_5032_){
_start:
{
lean_object* v_res_5033_; 
v_res_5033_ = l_Lean_Meta_Grind_registerAttr(v_attrName_5030_, v_ref_5031_);
return v_res_5033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_5034_, lean_object* v_m_5035_, lean_object* v_a_5036_, lean_object* v_b_5037_){
_start:
{
lean_object* v___x_5038_; 
v___x_5038_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_5035_, v_a_5036_, v_b_5037_);
return v___x_5038_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_5039_, lean_object* v_a_5040_, lean_object* v_x_5041_){
_start:
{
uint8_t v___x_5042_; 
v___x_5042_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_5040_, v_x_5041_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5043_, lean_object* v_a_5044_, lean_object* v_x_5045_){
_start:
{
uint8_t v_res_5046_; lean_object* v_r_5047_; 
v_res_5046_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_5043_, v_a_5044_, v_x_5045_);
lean_dec(v_x_5045_);
lean_dec(v_a_5044_);
v_r_5047_ = lean_box(v_res_5046_);
return v_r_5047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_5048_, lean_object* v_data_5049_){
_start:
{
lean_object* v___x_5050_; 
v___x_5050_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_5049_);
return v___x_5050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_5051_, lean_object* v_a_5052_, lean_object* v_b_5053_, lean_object* v_x_5054_){
_start:
{
lean_object* v___x_5055_; 
v___x_5055_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_5052_, v_b_5053_, v_x_5054_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5056_, lean_object* v_i_5057_, lean_object* v_source_5058_, lean_object* v_target_5059_){
_start:
{
lean_object* v___x_5060_; 
v___x_5060_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_5057_, v_source_5058_, v_target_5059_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_5061_, lean_object* v_x_5062_, lean_object* v_x_5063_){
_start:
{
lean_object* v___x_5064_; 
v___x_5064_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_5062_, v_x_5063_);
return v___x_5064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_5072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_5073_ = l_Lean_Meta_Grind_registerAttr(v___x_5071_, v___x_5072_);
return v___x_5073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_5074_){
_start:
{
lean_object* v_res_5075_; 
v_res_5075_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_5075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; 
v___x_5086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_5087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_5088_ = l_Lean_Meta_Grind_registerAttr(v___x_5086_, v___x_5087_);
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_5090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_5091_, lean_object* v_a_5092_){
_start:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v_env_5096_; lean_object* v___x_5097_; lean_object* v_ext_5098_; lean_object* v_toEnvExtension_5099_; lean_object* v_asyncMode_5100_; uint8_t v___x_5101_; lean_object* v___x_5102_; lean_object* v_casesTypes_5103_; uint8_t v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5094_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_5095_ = lean_st_ref_get(v_a_5092_);
v_env_5096_ = lean_ctor_get(v___x_5095_, 0);
lean_inc_ref(v_env_5096_);
lean_dec(v___x_5095_);
v___x_5097_ = l_Lean_Meta_Grind_grindExt;
v_ext_5098_ = lean_ctor_get(v___x_5097_, 1);
v_toEnvExtension_5099_ = lean_ctor_get(v_ext_5098_, 0);
v_asyncMode_5100_ = lean_ctor_get(v_toEnvExtension_5099_, 2);
v___x_5101_ = 0;
v___x_5102_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5094_, v___x_5097_, v_env_5096_, v_asyncMode_5100_, v___x_5101_);
v_casesTypes_5103_ = lean_ctor_get(v___x_5102_, 0);
lean_inc_ref(v_casesTypes_5103_);
lean_dec(v___x_5102_);
v___x_5104_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_5103_, v_declName_5091_);
lean_dec_ref(v_casesTypes_5103_);
v___x_5105_ = lean_box(v___x_5104_);
v___x_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5105_);
return v___x_5106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_){
_start:
{
lean_object* v_res_5110_; 
v_res_5110_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_5107_, v_a_5108_);
lean_dec(v_a_5108_);
lean_dec(v_declName_5107_);
return v_res_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v___x_5115_; 
v___x_5115_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_5111_, v_a_5113_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_){
_start:
{
lean_object* v_res_5120_; 
v_res_5120_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_5116_, v_a_5117_, v_a_5118_);
lean_dec(v_a_5118_);
lean_dec_ref(v_a_5117_);
lean_dec(v_declName_5116_);
return v_res_5120_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default = _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default);
l_Lean_Meta_Grind_instInhabitedNormSymTheorems = _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymTheorems);
l_Lean_Meta_Grind_instInhabitedNormSymEntry_default = _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymEntry_default);
l_Lean_Meta_Grind_instInhabitedNormSymEntry = _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymEntry);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normSymExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normSymExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_extensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_extensionMapRef);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_grindExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_grindExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_liaExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_liaExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1 = _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1);
l_Lean_Meta_Grind_registerAttr___auto__1 = _init_l_Lean_Meta_Grind_registerAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_Grind_registerAttr___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
