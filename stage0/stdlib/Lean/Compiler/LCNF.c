// Lean compiler output
// Module: Lean.Compiler.LCNF
// Imports: Init Lean.Meta.Match.MatcherInfo Lean.Meta.Transform Lean.Compiler.InlineAttrs Lean.Compiler.CompilerM
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
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_visitLetImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__1;
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitProj(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__2;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_mkFreshLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6___closed__1;
static lean_object* l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__2;
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_ToLCNF_State_cache___default___spec__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_isLCProof(lean_object*);
lean_object* l_Lean_Compiler_mkLetUsingScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_State_cache___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_noConfusionExt;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__6;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_ToLCNF_withNewRoot___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at_Lean_Compiler_shouldEtaExpand___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__10(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_ToLCNF_toLCNF_visitApp___spec__1(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldEtaExpand___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_withNewScopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_withNewRoot___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_ToLCNF_toLCNF_visitApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__2;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__4;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitApp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_ToLCNF_toLCNF_visitLambda___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__7;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLetDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_mkFreshLetDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_ToLCNF_State_cache___default___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__6___closed__1;
static lean_object* l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__1;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__8(lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__2;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_withNewRoot___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_ToLCNF_toLCNF_visitLambda___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__2;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isCompilerRelevantMData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__1;
static lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_ToLCNF_withNewRoot___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__11(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__3;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitMData___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitMData(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isLCProof___boxed(lean_object*);
static lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__5;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at_Lean_Compiler_shouldEtaExpand___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_isCompilerRelevantMData(lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldEtaExpand___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_ToLCNF_toLCNF_visitLambda___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitMData___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__11___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__4;
static lean_object* l_Lean_Compiler_isLCProof___closed__2;
static lean_object* l_Lean_Compiler_isLCProof___closed__1;
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_withNewRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_ToLCNF_withNewRoot___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitChild(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitMData___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__3;
static lean_object* _init_l_Lean_Compiler_isLCProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcProof", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_isLCProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_isLCProof___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isLCProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Compiler_isLCProof___closed__2;
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isLCProof___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isLCProof(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at_Lean_Compiler_shouldEtaExpand___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_isRecCore(x_8, x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_isRecCore(x_13, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldEtaExpand___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_is_matcher(x_8, x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_is_matcher(x_13, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 0;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_shouldEtaExpand___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Quot", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lift", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__3;
x_2 = l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__1;
x_7 = l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__5;
x_8 = lean_name_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_apply_4(x_6, x_9, x_3, x_4, x_5);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_dec(x_3);
lean_inc(x_1);
x_7 = l_Lean_Environment_isConstructor(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Compiler_shouldEtaExpand___lambda__2(x_1, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_3);
lean_inc(x_1);
x_7 = l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldEtaExpand___spec__2(x_1, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = l_Lean_Compiler_shouldEtaExpand___lambda__3(x_1, x_2, x_11, x_4, x_5, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_3);
lean_inc(x_1);
x_7 = l_Lean_isRec___at_Lean_Compiler_shouldEtaExpand___spec__1(x_1, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = l_Lean_Compiler_shouldEtaExpand___lambda__4(x_1, x_2, x_11, x_4, x_5, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_shouldEtaExpand___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_noConfusionExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
x_7 = l_Lean_Compiler_shouldEtaExpand___lambda__6___closed__1;
lean_inc(x_1);
lean_inc(x_2);
x_8 = l_Lean_TagDeclarationExtension_isTagged(x_7, x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Compiler_shouldEtaExpand___lambda__5(x_1, x_2, x_9, x_4, x_5, x_6);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
lean_inc(x_9);
x_10 = l_Lean_isCasesOnRecursor(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_5);
x_11 = lean_box(0);
x_12 = l_Lean_Compiler_shouldEtaExpand___lambda__6(x_1, x_9, x_11, x_2, x_3, x_8);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_1);
lean_inc(x_17);
x_18 = l_Lean_isCasesOnRecursor(x_17, x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_shouldEtaExpand___lambda__6(x_1, x_17, x_19, x_2, x_3, x_16);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at_Lean_Compiler_shouldEtaExpand___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isRec___at_Lean_Compiler_shouldEtaExpand___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldEtaExpand___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldEtaExpand___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_shouldEtaExpand___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldEtaExpand___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_shouldEtaExpand___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isCompilerRelevantMData(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isCompilerRelevantMData___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isCompilerRelevantMData(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_ToLCNF_State_cache___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_State_cache___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_ToLCNF_State_cache___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Compiler_ToLCNF_State_cache___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_mkFreshLetDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_2 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__2;
x_9 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_8, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_12 = l_Lean_Compiler_inferType(x_1, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = l_Lean_Compiler_mkLetDecl(x_10, x_13, x_1, x_15, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_mkFreshLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Compiler_ToLCNF_mkFreshLetDecl(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_ToLCNF_withNewRoot___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_2);
x_9 = lean_apply_2(x_1, x_8, x_3);
x_10 = l_Lean_Compiler_withNewScopeImp___rarg(x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_ToLCNF_withNewRoot___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_withNewScope___at_Lean_Compiler_ToLCNF_withNewRoot___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_withNewRoot___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
lean_inc(x_6);
lean_inc(x_3);
x_14 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_ToLCNF_withNewRoot___spec__1___rarg(x_1, x_13, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_6, x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_set(x_3, x_11, x_18);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_st_ref_get(x_6, x_25);
lean_dec(x_6);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_set(x_3, x_11, x_27);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_withNewRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_ToLCNF_withNewRoot___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_ToLCNF_withNewRoot___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_ToLCNF_withNewRoot___spec__1___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_withNewRoot___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Compiler_ToLCNF_withNewRoot___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitChild(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_Compiler_ToLCNF_toLCNF_visit(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__2;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__3;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__4;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_box(x_2);
x_11 = lean_apply_6(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Expr_hash(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_AssocList_foldlM___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__7(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_expr_eqv(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_expr_eqv(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__8(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__4(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__5(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__8(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Expr_hash(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__4(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__5(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__8(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_set(x_2, x_3, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_1 = x_10;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = l_Lean_Compiler_ToLCNF_toLCNF_visitApp(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__11(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
x_14 = l_Std_HashMap_insert___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__3(x_12, x_1, x_2);
x_15 = lean_st_ref_set(x_4, x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_Compiler_ToLCNF_toLCNF_visit(x_3, x_8, x_2, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_dec(x_2);
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_Compiler_ToLCNF_toLCNF_visitApp(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
case 5:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_18);
x_20 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__2;
lean_inc(x_19);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_19, x_22);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_24 = l_Lean_Expr_withAppAux___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__9(x_1, x_21, x_23, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
case 6:
{
lean_object* x_32; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_32 = l_Lean_Compiler_ToLCNF_toLCNF_visitLambda(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1(x_1, x_33, x_3, x_4, x_5, x_6, x_7, x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
case 8:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_box(x_3);
lean_inc(x_4);
x_41 = lean_alloc_closure((void*)(l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__2___boxed), 7, 2);
lean_closure_set(x_41, 0, x_40);
lean_closure_set(x_41, 1, x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_42 = l_Lean_Compiler_visitLetImp(x_1, x_41, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_45 = l_Lean_Compiler_ToLCNF_toLCNF_visit(x_43, x_3, x_4, x_5, x_6, x_7, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1(x_1, x_46, x_3, x_4, x_5, x_6, x_7, x_47);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 0);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_45);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_42);
if (x_53 == 0)
{
return x_42;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_42, 0);
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_42);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 9:
{
lean_object* x_57; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_57 = l_Lean_Compiler_ToLCNF_mkFreshLetDecl(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1(x_1, x_58, x_3, x_4, x_5, x_6, x_7, x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
case 10:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_66 = l_Lean_Compiler_ToLCNF_toLCNF_visit(x_65, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1(x_1, x_67, x_3, x_4, x_5, x_6, x_7, x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_66);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
case 11:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 2);
lean_inc(x_76);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_77 = l_Lean_Compiler_ToLCNF_toLCNF_visitProj(x_74, x_75, x_76, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1(x_1, x_78, x_3, x_4, x_5, x_6, x_7, x_79);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_77);
if (x_81 == 0)
{
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_77, 0);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_77);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
default: 
{
lean_object* x_85; 
lean_inc(x_1);
x_85 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1(x_1, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_85;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_2);
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_4, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_1);
x_15 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__10(x_13, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_11);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_14);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
lean_inc(x_1);
x_21 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__10(x_19, x_1);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_Compiler_isTypeFormerType(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__4(x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_isLCProof___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_9 = l_Lean_Compiler_inferType(x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_10);
x_12 = l_Lean_Compiler_isProp(x_10, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__5(x_10, x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6___closed__1;
x_21 = l_Lean_Expr_app___override(x_20, x_10);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6___closed__1;
x_24 = l_Lean_Expr_app___override(x_23, x_10);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
return x_9;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.ToLCNF.toLCNF.visit", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__1;
x_2 = l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__2;
x_3 = lean_unsigned_to_nat(112u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected occurrence of metavariable in code generator", 55);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 7);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 8);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 9);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 10);
lean_inc(x_18);
x_19 = lean_nat_dec_eq(x_11, x_12);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_5, 10);
lean_dec(x_21);
x_22 = lean_ctor_get(x_5, 9);
lean_dec(x_22);
x_23 = lean_ctor_get(x_5, 8);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 7);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 6);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 5);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 4);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 3);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_5, 0);
lean_dec(x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_11, x_32);
lean_dec(x_11);
lean_ctor_set(x_5, 3, x_33);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__4;
x_35 = l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1(x_34, x_2, x_3, x_4, x_5, x_6, x_7);
return x_35;
}
case 1:
{
lean_object* x_36; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_7);
return x_36;
}
case 2:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = l_Lean_indentExpr(x_1);
x_38 = l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__6;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__8;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__2(x_41, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_42;
}
case 3:
{
lean_object* x_43; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_7);
return x_43;
}
case 7:
{
lean_object* x_44; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
default: 
{
uint8_t x_45; 
x_45 = l_Lean_Compiler_isLCProof(x_1);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
x_47 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6(x_1, x_46, x_2, x_3, x_4, x_5, x_6, x_7);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_11, x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_9);
lean_ctor_set(x_51, 2, x_10);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_12);
lean_ctor_set(x_51, 5, x_13);
lean_ctor_set(x_51, 6, x_14);
lean_ctor_set(x_51, 7, x_15);
lean_ctor_set(x_51, 8, x_16);
lean_ctor_set(x_51, 9, x_17);
lean_ctor_set(x_51, 10, x_18);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_52 = l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__4;
x_53 = l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1(x_52, x_2, x_3, x_4, x_51, x_6, x_7);
return x_53;
}
case 1:
{
lean_object* x_54; 
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_7);
return x_54;
}
case 2:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = l_Lean_indentExpr(x_1);
x_56 = l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__6;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__8;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__2(x_59, x_2, x_3, x_4, x_51, x_6, x_7);
lean_dec(x_6);
lean_dec(x_51);
lean_dec(x_4);
lean_dec(x_3);
return x_60;
}
case 3:
{
lean_object* x_61; 
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
case 7:
{
lean_object* x_62; 
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_7);
return x_62;
}
default: 
{
uint8_t x_63; 
x_63 = l_Lean_Compiler_isLCProof(x_1);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_box(0);
x_65 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6(x_1, x_64, x_2, x_3, x_4, x_51, x_6, x_7);
return x_65;
}
else
{
lean_object* x_66; 
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_7);
return x_66;
}
}
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_67 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_67;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_ToLCNF_toLCNF_visitLambda___spec__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = lean_apply_6(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(x_3);
x_14 = lean_apply_7(x_2, x_11, x_13, x_4, x_5, x_6, x_7, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_ToLCNF_toLCNF_visitLambda___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_ToLCNF_toLCNF_visitLambda___spec__1___rarg___boxed), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_visitLambda(x_1, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Compiler_ToLCNF_toLCNF_visit(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_mkLetUsingScope(x_11, x_4, x_5, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_mkLambda(x_8, x_14, x_4, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_8);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__2___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__1___boxed), 7, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_ToLCNF_toLCNF_visitLambda___spec__1___rarg___boxed), 8, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Compiler_ToLCNF_withNewRoot___rarg(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_ToLCNF_mkFreshLetDecl(x_12, x_2, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitMData___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_ToLCNF_toLCNF_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitMData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_ToLCNF_toLCNF_visitMData___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Compiler_ToLCNF_toLCNF_visit(x_3, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_proj___override(x_1, x_2, x_12);
x_15 = l_Lean_Compiler_ToLCNF_mkFreshLetDecl(x_14, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_ToLCNF_toLCNF_visitApp___spec__1(size_t x_1, size_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Compiler_ToLCNF_toLCNF_visit(x_12, x_15, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_14, x_2, x_17);
x_2 = x_20;
x_3 = x_21;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitApp(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_ToLCNF_toLCNF_visitApp___spec__1(x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_mkAppN(x_1, x_13);
x_16 = l_Lean_Compiler_ToLCNF_mkFreshLetDecl(x_15, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitChild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Compiler_ToLCNF_toLCNF_visitChild(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_throwError___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Expr_withAppAux___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__9(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__4(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__5(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Compiler_ToLCNF_toLCNF_visit(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_ToLCNF_toLCNF_visitLambda___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_ReaderT_bind___at_Lean_Compiler_ToLCNF_toLCNF_visitLambda___spec__1___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___lambda__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Compiler_ToLCNF_toLCNF_visitLambda(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitMData___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Compiler_ToLCNF_toLCNF_visitMData___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitMData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_ToLCNF_toLCNF_visitMData(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Compiler_ToLCNF_toLCNF_visitProj(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_ToLCNF_toLCNF_visitApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Compiler_ToLCNF_toLCNF_visitApp___spec__1(x_10, x_11, x_3, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF_visitApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Compiler_ToLCNF_toLCNF_visitApp(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_ToLCNF_toLCNF___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_ToLCNF_toLCNF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_6 = l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_st_ref_get(x_4, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_mk_ref(x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Compiler_ToLCNF_toLCNF___closed__1;
x_16 = lean_st_mk_ref(x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
lean_inc(x_4);
lean_inc(x_11);
lean_inc(x_17);
x_20 = l_Lean_Compiler_ToLCNF_toLCNF_visit(x_2, x_19, x_17, x_11, x_3, x_4, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_4, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_17, x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_4, x_26);
lean_dec(x_4);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_get(x_11, x_28);
lean_dec(x_11);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_LocalContext_mkLambda(x_32, x_33, x_21);
lean_dec(x_33);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Lean_LocalContext_mkLambda(x_37, x_38, x_21);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_InlineAttrs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InlineAttrs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_isLCProof___closed__1 = _init_l_Lean_Compiler_isLCProof___closed__1();
lean_mark_persistent(l_Lean_Compiler_isLCProof___closed__1);
l_Lean_Compiler_isLCProof___closed__2 = _init_l_Lean_Compiler_isLCProof___closed__2();
lean_mark_persistent(l_Lean_Compiler_isLCProof___closed__2);
l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__1 = _init_l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__1);
l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__2 = _init_l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__2);
l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__3 = _init_l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__3);
l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__4 = _init_l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__4);
l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__5 = _init_l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Compiler_shouldEtaExpand___lambda__2___closed__5);
l_Lean_Compiler_shouldEtaExpand___lambda__6___closed__1 = _init_l_Lean_Compiler_shouldEtaExpand___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Compiler_shouldEtaExpand___lambda__6___closed__1);
l_Lean_Compiler_ToLCNF_State_cache___default = _init_l_Lean_Compiler_ToLCNF_State_cache___default();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_State_cache___default);
l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__1 = _init_l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__1);
l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__2 = _init_l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__2();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_mkFreshLetDecl___closed__2);
l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__1);
l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__2);
l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__3 = _init_l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__3);
l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__4 = _init_l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__1___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_ToLCNF_toLCNF_visit___spec__12___closed__2);
l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__1 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__1);
l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__2 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__3___closed__2);
l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6___closed__1 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visit___lambda__6___closed__1);
l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__1 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__1();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__1);
l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__2 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__2();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__2);
l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__3 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__3();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__3);
l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__4 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__4();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__4);
l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__5 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__5();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__5);
l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__6 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__6();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__6);
l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__7 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__7();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__7);
l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__8 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__8();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visit___closed__8);
l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___closed__1 = _init_l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___closed__1();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF_visitLambda___closed__1);
l_Lean_Compiler_ToLCNF_toLCNF___closed__1 = _init_l_Lean_Compiler_ToLCNF_toLCNF___closed__1();
lean_mark_persistent(l_Lean_Compiler_ToLCNF_toLCNF___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
