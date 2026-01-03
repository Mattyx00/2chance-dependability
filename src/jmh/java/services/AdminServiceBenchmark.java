package services;

import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.io.IOException;
import java.sql.SQLException;
import java.util.concurrent.TimeUnit;

@State(Scope.Thread)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
public class AdminServiceBenchmark {

    private AdminService adminService;

    @Setup(Level.Trial)
    public void setup() throws SQLException {
        this.adminService = new AdminService();
    }

    @Benchmark
    public void benchmarkGetProdottoNotFound(Blackhole bh) {
        try {
            // Benchmark the exception path for "Product Not Found"
            // This includes service validation and DAO lookup
            adminService.getProdotto(99999);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (IOException | SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkInfoOrdineNotFound(Blackhole bh) {
        try {
            // Benchmark the exception path for "Order Not Found"
            adminService.infoOrdine(99999);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (IOException | SQLException e) {
            bh.consume(e);
        }
    }
}
