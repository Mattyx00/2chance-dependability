package utils;

import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.sql.Connection;
import java.sql.SQLException;
import java.util.concurrent.TimeUnit;

@State(Scope.Thread)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
public class ConnectionPoolBenchmark {

    @Setup(Level.Trial)
    public void setup() {
        // Trigger lazy initialization of the pool before benchmark starts
        try (Connection ignored = ConPool.getConnection()) {
            // Pool initialized
        } catch (SQLException e) {
            System.err.println("WARNING: Database not available? Benchmark might fail or timeout.");
        }
    }

    @Benchmark
    public void benchmarkGetReleaseConnection(Blackhole bh) throws SQLException {
        try (Connection conn = ConPool.getConnection()) {
            bh.consume(conn);
        }
    }
}
