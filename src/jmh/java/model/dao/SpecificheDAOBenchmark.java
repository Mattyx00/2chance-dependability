package model.dao;

import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.sql.SQLException;
import java.util.concurrent.TimeUnit;

@State(Scope.Thread)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
public class SpecificheDAOBenchmark {

    private SpecificheDAO specificheDAO;

    @Setup(Level.Trial)
    public void setup() {
        this.specificheDAO = new SpecificheDAO();
    }

    @Benchmark
    public void benchmarkGetSpecificheInvalidId(Blackhole bh) {
        try {
            specificheDAO.getSpecificheByProd(-1);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetSpecificheValidId(Blackhole bh) {
        try {
            // This attempts a DB call. If DB is offline, it catches SQLException.
            // If DB is online, it measures query performance.
            specificheDAO.getSpecificheByProd(1);
        } catch (SQLException e) {
            bh.consume(e);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        }
    }
}
