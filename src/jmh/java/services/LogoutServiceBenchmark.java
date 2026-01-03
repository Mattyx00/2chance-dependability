package services;

import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import javax.servlet.http.HttpSession;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;
import java.util.concurrent.TimeUnit;

@State(Scope.Thread)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
public class LogoutServiceBenchmark {

    private LogoutService logoutService;
    private HttpSession dummySession;

    @Setup(Level.Trial)
    public void setup() {
        logoutService = new LogoutService();
        dummySession = (HttpSession) Proxy.newProxyInstance(
                HttpSession.class.getClassLoader(),
                new Class[]{HttpSession.class},
                new InvocationHandler() {
                    @Override
                    public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {
                        // Minimal implementation: do nothing for invalidate
                        return null;
                    }
                }
        );
    }

    @Benchmark
    public void benchmarkLogoutValidSession(Blackhole bh) {
        logoutService.logout(dummySession);
        bh.consume(dummySession);
    }
}
