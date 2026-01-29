// Lean compiler output
// Module: Lean.Compiler.LCNF
// Imports: public import Lean.Compiler.LCNF.AlphaEqv public import Lean.Compiler.LCNF.Basic public import Lean.Compiler.LCNF.Bind public import Lean.Compiler.LCNF.Check public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.CSE public import Lean.Compiler.LCNF.DependsOn public import Lean.Compiler.LCNF.ElimDead public import Lean.Compiler.LCNF.FixedParams public import Lean.Compiler.LCNF.InferType public import Lean.Compiler.LCNF.JoinPoints public import Lean.Compiler.LCNF.LCtx public import Lean.Compiler.LCNF.Level public import Lean.Compiler.LCNF.Main public import Lean.Compiler.LCNF.Passes public import Lean.Compiler.LCNF.PassManager public import Lean.Compiler.LCNF.PhaseExt public import Lean.Compiler.LCNF.PrettyPrinter public import Lean.Compiler.LCNF.PullFunDecls public import Lean.Compiler.LCNF.PullLetDecls public import Lean.Compiler.LCNF.ReduceJpArity public import Lean.Compiler.LCNF.Simp public import Lean.Compiler.LCNF.Specialize public import Lean.Compiler.LCNF.SpecInfo public import Lean.Compiler.LCNF.Testing public import Lean.Compiler.LCNF.ToDecl public import Lean.Compiler.LCNF.ToExpr public import Lean.Compiler.LCNF.ToLCNF public import Lean.Compiler.LCNF.Types public import Lean.Compiler.LCNF.Util public import Lean.Compiler.LCNF.ConfigOptions public import Lean.Compiler.LCNF.MonoTypes public import Lean.Compiler.LCNF.ToMono public import Lean.Compiler.LCNF.MonadScope public import Lean.Compiler.LCNF.Closure public import Lean.Compiler.LCNF.LambdaLifting public import Lean.Compiler.LCNF.ReduceArity public import Lean.Compiler.LCNF.Probing public import Lean.Compiler.LCNF.Irrelevant public import Lean.Compiler.LCNF.SplitSCC
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
lean_object* initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Check(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_FixedParams(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_JoinPoints(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_LCtx(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Level(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Main(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Passes(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PullFunDecls(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Specialize(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_SpecInfo(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Testing(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ConfigOptions(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToMono(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_LambdaLifting(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Probing(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Irrelevant(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_SplitSCC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Bind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CSE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_JoinPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_LCtx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Passes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Specialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Testing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToLCNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToMono(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonadScope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Probing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_SplitSCC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
