// Lean compiler output
// Module: PF_L4L
// Imports: Init PF_L4L.Core.Resonance PF_L4L.Core.Zeta PF_L4L.Core.SpectralGap PF_L4L.Core.AxiomAudit PF_L4L.Ch20.RH PF_L4L.Ch21.PNP PF_L4L.Ch23.YM PF_L4L.Ch24.BSD
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_PF__L4L_Core_Resonance(uint8_t builtin, lean_object*);
lean_object* initialize_PF__L4L_Core_Zeta(uint8_t builtin, lean_object*);
lean_object* initialize_PF__L4L_Core_SpectralGap(uint8_t builtin, lean_object*);
lean_object* initialize_PF__L4L_Core_AxiomAudit(uint8_t builtin, lean_object*);
lean_object* initialize_PF__L4L_Ch20_RH(uint8_t builtin, lean_object*);
lean_object* initialize_PF__L4L_Ch21_PNP(uint8_t builtin, lean_object*);
lean_object* initialize_PF__L4L_Ch23_YM(uint8_t builtin, lean_object*);
lean_object* initialize_PF__L4L_Ch24_BSD(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PF__L4L(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PF__L4L_Core_Resonance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PF__L4L_Core_Zeta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PF__L4L_Core_SpectralGap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PF__L4L_Core_AxiomAudit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PF__L4L_Ch20_RH(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PF__L4L_Ch21_PNP(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PF__L4L_Ch23_YM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PF__L4L_Ch24_BSD(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
