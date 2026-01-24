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
public class OrdineDAOBenchmark {

    private OrdineDAO ordineDAO;

    @Setup(Level.Trial)
    public void setup() {
        this.ordineDAO = new OrdineDAO();
    }

    @Benchmark
    public void benchmarkGetProdottoOrdineNull(Blackhole bh) {
        try {
            ordineDAO.getProdottoOrdine(null);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            // Should not happen for null input as validation is first
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetOrdineByIdInvalid(Blackhole bh) {
        try {
            ordineDAO.getOrdineById(-1);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetOrdineByIdValid(Blackhole bh) {
        try {
            // Happy Path: Retrieve valid order (ID 1)
            // This measures the real DB access time
            ordineDAO.getOrdineById(1);
        } catch (Exception e) {
            bh.consume(e);
        }
    }
}
