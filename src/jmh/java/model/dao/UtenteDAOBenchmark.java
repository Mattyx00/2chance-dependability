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
public class UtenteDAOBenchmark {

    private UtenteDAO utenteDAO;

    @Setup(Level.Trial)
    public void setup() {
        utenteDAO = new UtenteDAO();
    }

    @Benchmark
    public void benchmarkGetUtenteByIdNotFound(Blackhole bh) {
        try {
            // 99999 is assumed to not exist. If it does, it returns a Utente object.
            // Both paths are valid for benchmarking the "Attempt to find" logic.
            bh.consume(utenteDAO.getUtenteById(99999));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }
}
